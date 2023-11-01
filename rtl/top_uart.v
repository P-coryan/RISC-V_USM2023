module tt_um_uart (
    clk,
    reset,
    instr_rx, 
    mem_rx,
    mem_tx,
    instr_tx,
    pc,
    write_enable,
    read_enable,
    address,
    write_data,
    cpu_reset,
    cpu_run,
    read_data,
    mem_done,
    uart_data
);
input wire clk;
input wire reset;
input wire instr_rx; 
input wire  mem_rx;
output wire  mem_tx;
output wire instr_tx;

// CPU COM CONTROLLER INSTANCE
input wire [31:0] pc;         // antes era solo wire 
input wire write_enable;
input wire read_enable;
input wire [31:0] address;
input wire [31:0] write_data;
output wire cpu_reset, cpu_run;
output wire [31:0] read_data; 
output wire  mem_done; 
output wire [31:0] uart_data;

cpu_com_controller com_controller(
    .clk (clk),
    .reset (reset),
    .rx (instr_rx),
    .pc (pc),
    .tx (instr_tx),
    .cpu_reset (cpu_reset),
    .cpu_run (cpu_run),
    .uart_data(uart_data)
);


// MEMORY COM CONTROLLER INSTANCE
memory_com memory_communitacion(
    .clk (clk),
    .reset (reset),
    .rx (mem_rx),
    .tx (mem_tx),
    .write_enable (write_enable),
    .read_enable (read_enable ),
    .mem_done (mem_done),
    .writeData (write_data),
    .readData (read_data),
    .address (address)
);
 
endmodule
