`timescale 1ns / 1ps

module tbMemory_com ();

logic clk,reset;
    
// UART Communication
logic rx;
logic tx;

// CPU Control
logic write_enable;
logic read_enable;
logic mem_done;

// CPU Data
logic [7:0] writeData;
logic [7:0] readData;
logic [7:0] address;
logic [2:0]  SizeLoad;
logic [1:0]  MemWrite;

memory_com memcom (
    .clk (clk),
    .reset (reset),
    .rx (rx),
    .tx (tx),
    .write_enable (write_enable),
    .read_enable (read_enable),
    .mem_done (mem_done),
    .writeData (writeData),
    .readData (readData),
    .address (address),
    .SizeLoad (SizeLoad),
    .MemWrite (MemWrite)
);

// UART to test reception
logic send_start;
logic [7:0] send_data;
logic send_ready;

uart_sm_tx uart_tx(
    .clk        ( clk ),
    .reset      ( reset ),
    .send_pulse ( send_start ),
    .byte_in    ( send_data),
    .tx         (rx),
    .byte_end   (send_ready)
    );

assign writeData = 8'b01;
assign address = 8'b11;
assign SizeLoad = 3'b100;
assign MemWrite = 2'b10;

assign send_data = 8'b1010_1010;

// Clock.
always begin
    clk = 1'b1; 
    #10;
    clk = 1'b0;
    #10;
end

initial begin
    // Initial Values.
    write_enable = 1'b0;
    read_enable = 1'b0;
    send_start = 1'b0;

    // Reset.
    reset = 1'b1;
    #20;
    reset = 1'b0;
    #20;

    // Write.
    write_enable = 1'b1;

    #10000;
    write_enable = 1'b0;
    #30000;

    // Read.
    read_enable = 1'b1;
    #10000;

    read_enable = 1'b0;
    #20000;

    send_start = 1'b1;
    #20;
    send_start = 1'b0;
    #15000;

    // Back to Initial Values.
    write_enable = 1'b0;
    read_enable = 1'b0;
    send_start = 1'b0;

    $finish;
end

endmodule