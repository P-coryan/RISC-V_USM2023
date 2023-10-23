module uart_32bit_tx(
    input wire clk,
    input wire reset,
    input wire send_start,
    input wire [31:0] data_in,
    output reg tx,
    output reg data_end
);

// UART Instances
reg        byte_start;
reg [7:0]  send_data;
reg        send_ready;

uart_32bit_tx uart_tx(
    .clk        ( clk ),
    .reset      ( reset ),
    .send_pulse ( byte_start ),
    .byte_in    ( send_data ),
    .tx         ( tx ),
    .byte_end   ( send_ready )
);

// FSM States
localparam  IDLE       = 3'b000,
            SEND_BYTE1 = 3'b001,
            SEND_BYTE2 = 3'b010,
            SEND_BYTE3 = 3'b011,
            SEND_BYTE4 = 3'b100,
            DONE       = 3'b101;

reg [2:0] state;
reg [2:0] next_state;  

always @(posedge clk) begin
    if(reset) begin
        state <= IDLE;
    end
    else begin
        state <= next_state;
    end
end

reg      rst_data;
reg       save;
reg [1:0] save_ctrl;

always @(*) begin
    next_state = IDLE;
    byte_start = 0;
    data_end = 0;

    case(state)
        IDLE: begin
            if(send_start) next_state = SEND_BYTE1;
            else next_state = IDLE;
        end
        SEND_BYTE1: begin
            byte_start = 1;
            send_data = data_in[7:0];
            if(send_ready) next_state = SEND_BYTE2;
            else next_state = SEND_BYTE1;
        end
        SEND_BYTE2: begin
            byte_start = 1;
            send_data = data_in[15:8];
            if(send_ready) next_state = SEND_BYTE3;
            else next_state = SEND_BYTE2;
        end
        SEND_BYTE3: begin
            byte_start = 1;
            send_data = data_in[23:16];
            if(send_ready) next_state = SEND_BYTE4;
            else next_state = SEND_BYTE3;
        end
        SEND_BYTE4: begin
            byte_start = 1;
            send_data = data_in[31:24];
            if(send_ready) next_state = DONE;
            else next_state = SEND_BYTE4;
        end
        DONE: begin
            data_end = 1;
            next_state = IDLE;
        end
    endcase
end

endmodule