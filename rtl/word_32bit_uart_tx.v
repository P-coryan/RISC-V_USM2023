//////////////////////////////////////////////////////////////////////////////////
// Company: 
// Engineer: 
// 
// Create Date: 31.01.2022 12:19:03
// Design Name: 
// Module Name: word_32bit_uart_tx
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


module word_32bit_uart_tx(
    input wire clk, reset,
    input wire addr_query,
    input wire [31:0] addr,
    output wire tx,
    output reg word_send
    );
    
    //byte query --------------------------------------------------------------------------------------
    
    reg byte_query;
    wire byte_end;
    reg [7:0] byte_data;
    reg [7:0] pre_byte_data;
    
    always @(posedge clk) begin
        if(reset) byte_data <= 0;
        else byte_data <= pre_byte_data;
    end
    
    wire pre_tx;
    
    assign tx = addr_query ? pre_tx : 1'h1;
    
    uart_sm_tx byte_tx(clk,reset,byte_query,byte_data,pre_tx,byte_end);
    
    //byte count --------------------------------------------------------------------------------------
    
    reg [2:0] byte_contador;
    reg [2:0] pre_byte_contador;
    
    always @(posedge clk) begin
        if(reset) byte_contador <= 0;
        else byte_contador <= pre_byte_contador;
    end
    
    //state machine --------------------------------------------------------------------------------------
    
    localparam IDLE = 0;
    localparam START = 1;
    localparam SEND1 = 2;
    localparam SEND2 = 3;
    localparam WAITT = 4;
    
    reg [2:0] state;
    reg [2:0] next_state;
    
    always @(posedge clk) begin
        if(reset) state <= IDLE;
        else state <= next_state;
    end
    
    always @(*) begin
        next_state= state;
        pre_byte_contador = byte_contador;
        byte_query = 0;
        word_send = 0;
        pre_byte_data = byte_data;
        case(state)
            IDLE: begin
                if(addr_query) begin
                    next_state = START;
                    pre_byte_contador = 0;
                end
            end
            START: begin
                pre_byte_contador = byte_contador + 1;
                case(byte_contador)
                    0: begin
                        pre_byte_data = addr[7:0];
                        next_state = SEND1;
                    end
                    1: begin
                        pre_byte_data = addr[15:8];
                        next_state = SEND1;
                    end
                    2: begin
                        pre_byte_data = addr[23:16];
                        next_state = SEND1;
                    end
                    3: begin
                        pre_byte_data = addr[31:24];
                        next_state = SEND1;
                    end
                    4: begin
                        next_state = IDLE;
                        word_send = 1;
                    end
                endcase
            end
            SEND1: begin
                byte_query = 1;
                next_state = SEND2;
            end
            SEND2: begin
                byte_query = 1;
                next_state = WAITT;
            end
            WAITT: begin
                if(byte_end) next_state = START;
            end
        endcase
    end
endmodule
