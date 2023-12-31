//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 03/17/2022 01:04:30 PM
// Design Name: 
// Module Name: cpu_com_controller
// Project Name: 
// Target Devices: 
// Tool Versions: 
// Description: 
// 
// Dependencies: 
// 
// Revision:
// Revision 0.01 - File Created
// Additional Comments:
// 
//////////////////////////////////////////////////////////////////////////////////


module cpu_com_controller(
    input wire clk,reset,rx,
    input wire [31:0] pc,
    output reg tx,cpu_reset,cpu_run,
    output reg [31:0] uart_data,
    output reg cmd_redy,cmd_send,instr_send,
    output reg [2:0] state
    );
    
    localparam IDLE = 0;
    localparam WAIT_CMD = 1;
    localparam RESET_CPU = 2;
    localparam SEND_PC = 3;
    localparam RUN_CPU = 4;
    localparam CPU_REDY = 5;
    localparam WAIT_INST = 6;
    
    reg [2:0] next_state;
    
    wire div_clk;
    
    always @(posedge div_clk) begin
        if(reset) state <= IDLE;
        else state <= next_state;
    end
    
    //logic cmd_redy;
    reg cpu_redy;
    reg send_pc;
    
    //logic cmd_send,instr_send;
    
    clock_divider #(163) div(clk,reset, div_clk);
    
    wire PB_pressed_status,PB_pressed_pulse,PB_released_pulse;
    wire PB_pressed_status2,PB_pressed_pulse2,PB_released_pulse2;
    wire PB_pressed_status3,PB_pressed_pulse3,PB_released_pulse3;
    
    PB_Debouncer_FSM #(1) pb1(div_clk,reset,cmd_redy,PB_pressed_status,PB_pressed_pulse,PB_released_pulse);
    PB_Debouncer_FSM #(1) pb2(div_clk,reset,cmd_send,PB_pressed_status2,PB_pressed_pulse2,PB_released_pulse2);
    PB_Debouncer_FSM #(1) pb3(div_clk,reset,instr_send,PB_pressed_status3,PB_pressed_pulse3,PB_released_pulse3);
    
    word_32_bit_uart_rx uart_rx(div_clk,reset,rx,uart_data,cmd_redy);
    wire tx_1;
    word_32bit_uart_tx uart_send_redy(div_clk,reset,cpu_redy,32'd3,tx_1 ,cmd_send); //juntar ambos send en uno solo con un multiplexor dentro
    word_32bit_uart_tx uart_tx(div_clk,reset,send_pc,pc,tx,instr_send);
    
    always @(*) begin
        next_state = state;
        cpu_redy = 0;
        cpu_reset = 0;
        cpu_run = 0;
        send_pc = 0;
        case(state)
            IDLE: begin
                if(cmd_redy && uart_data == 1) begin
                    next_state = RESET_CPU; 
                end
            end
            WAIT_CMD: begin
                if(cmd_redy && uart_data == 2) begin
                    next_state = SEND_PC;
                end
            end
            RESET_CPU: begin
                cpu_reset = 1;
                next_state = CPU_REDY;
            end
            CPU_REDY: begin
                cpu_redy = 1;
                if(cmd_send) next_state = WAIT_CMD;
            end
            SEND_PC: begin
                send_pc = 1;
                if(instr_send) next_state = WAIT_INST;
            end
            WAIT_INST: begin
                if(PB_pressed_pulse) begin
                    next_state = RUN_CPU;
                end
            end
            RUN_CPU: begin
                cpu_run = 1;
                next_state = CPU_REDY;
            end
        endcase
    end
    
endmodule
