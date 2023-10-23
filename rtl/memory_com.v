`timescale 1ns / 1ps

module memory_com (
    input wire clk,reset,
    
    // UART Communication
    input wire rx,
    output wire tx,

    // CPU Control
    input  wire write_enable,
    input  wire read_enable,
    output reg  mem_done,

    // CPU Data
    input  wire [31:0] writeData,
    output reg  [31:0] readData,
    input  wire [31:0] address
);

// FSM States
localparam  IDLE = 3'b000,
            SEND_ADDRESS = 3'b001,
            WAIT_RECV_DATA = 3'b010,
            RECV_DATA = 3'b011,
            SEND_DATA = 3'b100,
            DONE = 3'b101;

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

// UART Instances
reg [31:0] recv_data;
reg        recv_ready;
reg        send_start;
reg [31:0] send_data;
reg        send_ready;

uart_32bit_rx uart_rx (
    .clk      ( clk ),
    .reset    ( reset ),
    .rx       ( rx ),
    .data_out ( recv_data ),
    .data_end ( recv_ready )
);

uart_32bit_tx uart_tx(
    .clk        ( clk ),
    .reset      ( reset ),
    .send_start ( send_start ),
    .data_in    ( send_data ),
    .tx         ( tx ),
    .data_end   ( send_ready )
);


reg [7:0] readData_prev;
always @(posedge clk) begin
    if(reset) begin
        readData_prev <= 'b0;
    end
    else begin
        readData_prev <= readData;
    end
end

always @(*) begin
    next_state = IDLE;
    
    send_start = 0;
    send_data = 0;

    mem_done = 0;

    readData = readData_prev;

    case(state)
        IDLE: begin
            readData = 0;
            if( write_enable || read_enable ) next_state = SEND_ADDRESS;
            else next_state = IDLE;
        end
        SEND_ADDRESS: begin
            send_start = 1;
            send_data = address;
            if( send_ready && write_enable ) next_state = SEND_DATA;
            else if ( send_ready && read_enable ) next_state = WAIT_RECV_DATA;
            else next_state = SEND_ADDRESS;
        end
        WAIT_RECV_DATA: begin
            if( recv_ready ) next_state = RECV_DATA;
            else next_state = WAIT_RECV_DATA;
        end
        RECV_DATA: begin
            readData = recv_data;
            next_state = DONE;
        end
        SEND_DATA: begin
            send_start = 1;
            send_data = writeData;
            if( send_ready ) next_state = DONE;
            else next_state = SEND_DATA;
        end
        DONE: begin
            mem_done = 1;
            next_state = IDLE;
        end
    endcase
end

endmodule

/*

Write: 
    
if(write_enable) enviar esto:
    address
    writeData
    MemWrite

Read:

if(read_enable) enviar:
    address
    SizeLoad
y recibir:
    readData

*/