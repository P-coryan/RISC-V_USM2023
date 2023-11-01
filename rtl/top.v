module tt_top_riscv (
    clk,
    reset,
    instr_rx, 
    mem_rx,
    mem_tx,
    instr_tx
);
input wire clk;
input wire reset;
input wire instr_rx; 
input wire  mem_rx;
output wire  mem_tx;
output wire instr_tx;



wire [31:0] pc;         // antes era solo wire 
wire write_enable;    //new
wire read_enable;     //new
wire [31:0] address;
wire [31:0] write_data ; 
wire cpu_reset, cpu_run;
wire [31:0]  read_data;
wire mem_done;
wire [31:0] uart_data;


tt_um_uart tt_um_uart (
    .clk(clk),
    .reset(reset),
    .instr_rx(instr_rx), 
    .mem_rx(mem_rx),
    .mem_tx(mem_tx),
    .instr_tx(instr_tx),
    .pc(pc),
    .write_enable(write_enable),
    .read_enable(read_enable),
    .address(address),
    .write_data(write_data),
    .cpu_reset(cpu_reset),
    .cpu_run(cpu_run),
    .read_data(read_data),
    .mem_done(mem_done),
    .uart_data(uart_data)

);


tt_um_single_cycle_datapath CPU (
	.clk (cpu_run),
	.rst (cpu_reset),
	.instr (uart_data),
	.addr (address),
	.alu_result (write_data),
	.read_data (read_data),
	.write_enable(write_enable),
    .read_enable (read_enable),
    .mem_done (mem_done),
    .pc (pc)
);


endmodule
