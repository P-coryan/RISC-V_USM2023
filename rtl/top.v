`timescale 1ns / 1ps

module top (
    input wire clk, reset,
    input wire instr_rx, mem_rx,
    output reg instr_tx, mem_tx
);

// CPU COM CONTROLLER INSTANCE
wire [31:0] pc;
wire cpu_reset, cpu_run;
wire [31:0] uart_data;

cpu_com_controller com_controller(
    .clk (clk),
    .reset (reset),
    .rx (instr_rx),
    .pc (pc),
    .tx (instr_tx),
    .cpu_reset (cpu_reset),
    .cpu_run (cpu_run),
    .uart_data (uart_data),
    .cmd_redy ( /* NOT CONNECTED */ ),
    .cmd_send ( /* NOT CONNECTED */ ),
    .instr_send ( /* NOT CONNECTED */ ),
    .state ( /* NOT CONNECTED */ )
);

// SINGLE CYCLE CPU INSTANCE
wire [31:0] address, write_data, read_data;
wire write_enable, read_enable;
reg mem_done ;  

tt_um_single_cycle_datapath CPU (
	.clk (clk),
	.rst (reset),
	.instr (uart_data),
	.addr (address),
	.alu_result (write_data),
	.read_data (read_data),
	.write_enable (write_enable),
    .read_enable ( read_enable),
    .mem_done (mem_done)
);

// MEMORY COM CONTROLLER INSTANCE
memory_com memory_communitacion(
    .clk (clk),
    .reset (reset),
    .rx (mem_rx),
    .tx (mem_tx),
    .write_enable (write_enable),
    .read_enable ( read_enable ),
    .mem_done (mem_done ),
    .writeData (write_data),
    .readData (read_data),
    .address (address)
);
    
endmodule
