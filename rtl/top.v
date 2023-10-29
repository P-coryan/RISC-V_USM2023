module top (
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
output reg  mem_tx;
output wire instr_tx;

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
    .uart_data (uart_data)
);


// SINGLE CYCLE CPU INSTANCE
wire [31:0] address, write_data, read_data;
wire write_enable, read_enable;
wire mem_done;  

tt_um_single_cycle_datapath CPU (
	.clk (cpu_run),
	.rst (cpu_reset),
	.instr (uart_data),
	.addr (address),
	.alu_result (write_data),
	.read_data (read_data),
	.write_enable (write_enable),
    .read_enable ( read_enable),
    .mem_done (mem_done),
    .pc (pc)
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

module tt_um_single_cycle_datapath (
	clk,
	rst,
	instr,
	addr,
	alu_result,
	read_data,
	write_enable,
	read_enable,
	mem_done,
	pc
);
	input wire clk;
	input wire rst;
	input wire [31:0] instr;
	output wire [31:0] addr;
	output wire [31:0] alu_result;
	input wire [31:0] read_data;
	output wire write_enable;
	output reg read_enable;
	input wire mem_done;
	output reg [31:0] pc;
	reg [31:0] pc_next;
	localparam signed [31:0] rv32i_defs_InstructionSize = 32;
	
	localparam signed [31:0] rv32i_defs_OperandSize = 32;
	wire [31:0] imm_ext;
	wire [31:0] pc_target;
	assign pc_target = imm_ext + pc;
	wire pc_src;
	always @(*)
		case (pc_src)
			'd0: pc_next = pc + 'd4;
			'd1: pc_next = pc_target;
			default: pc_next = 'bx;
		endcase
	always @(posedge clk) begin
		if (rst)
			pc <= 'b0;
		else
			if (~read_enable && ~write_enable) pc <= pc_next;
			else if (mem_done) pc <= pc_next;
			else pc <= pc;	// puede ser redundante (no se si es necesario)
	end
		
	assign addr = pc;
	wire reg_write;
	wire [31:0] read_data_1;
	wire [31:0] read_data_2;
	reg [31:0] result;
	register_file register_file(
		.clk(clk),
		.rst(rst),
		.addr_1(instr[19:15]),
		.addr_2(instr[24:20]),
		.addr_3(instr[11:7]),
		.write_enable_3(reg_write),
		.write_data_3(result),
		.read_data_1(read_data_1),
		.read_data_2(read_data_2)
	);
	wire [1:0] result_src;
	wire [1:0] imm_src;
	wire [2:0] alu_ctrl;
	wire alu_src;
	wire alu_status_zero;
	wire jump;
	wire branch;
	wire branch_alu_neg;
	control_unit control_unit(
		.opcode(instr[6:0]),
		.funct_3(instr[14:12]),
		.funct_7(instr[31:25]),
		.result_src(result_src),
		.mem_write(write_enable),
		.alu_ctrl(alu_ctrl),
		.alu_src(alu_src),
		.imm_src(imm_src),
		.reg_write(reg_write),
		.jump(jump),
		.branch(branch),
		.branch_alu_neg(branch_alu_neg)
	);
	jump_control jump_control(
		.jump(jump),
		.branch(branch),
		.branch_alu_neg(branch_alu_neg),
		.zero(alu_status_zero),
		.pc_src(pc_src)
	);
	imm_extend imm_extend(
		.imm_src(imm_src[1:0]),
		.instr(instr[31:7]),
		.imm_ext(imm_ext[31:0])
	);
	reg [31:0] src_b;
	always @(*)
		case (alu_src)
			'd0: src_b = read_data_2;
			'd1: src_b = imm_ext;
			default: src_b = 'bx;
		endcase
	wire [3:0] alu_status;
	assign alu_status_zero = alu_status[2];
	alu alu(
		.a(read_data_1),
		.b(src_b),
		.operation(alu_ctrl),
		.result(alu_result),
		.status(alu_status)
	);
	always @(*) begin
		read_enable = 0;
		case (result_src)
			'b0: result = alu_result;
			'b1: begin
				result = read_data;
				read_enable = 1;
			end
			'b10: result = pc + 'd4;
			'b11: result = 'bx;
			default: result = 'bx;
		endcase
	end
endmodule
module register_file (
	clk,
	rst,
	addr_1,
	addr_2,
	addr_3,
	write_enable_3,
	write_data_3,
	read_data_1,
	read_data_2
);
	input wire clk;
	input wire rst;
	localparam signed [31:0] rv32i_defs_NumRegisters = 32;
	localparam signed [31:0] rv32i_defs_RegisterSize = 5;
	input wire [4:0] addr_1;
	input wire [4:0] addr_2;
	input wire [4:0] addr_3;
	input wire write_enable_3;
	localparam signed [31:0] rv32i_defs_OperandSize = 32;
	input wire [31:0] write_data_3;
	output reg [31:0] read_data_1;
	output reg [31:0] read_data_2;
	reg [1023:rv32i_defs_OperandSize] mem;
	reg [31:0] zero;
	always @(*) begin
		zero = 'd0;
		if (addr_1 == 'd0)
			read_data_1 = zero;
		else
			read_data_1 = mem[addr_1 * rv32i_defs_OperandSize+:rv32i_defs_OperandSize];
		if (addr_2 == 'd0)
			read_data_2 = zero;
		else
			read_data_2 = mem[addr_2 * rv32i_defs_OperandSize+:rv32i_defs_OperandSize];
	end
	function automatic [31:0] sv2v_cast_F3D6C;
		input reg [31:0] inp;
		sv2v_cast_F3D6C = inp;
	endfunction
	always @(posedge clk)
		if (rst) begin
			mem <= {31 {sv2v_cast_F3D6C(1'sb0)}};
			mem[64+:rv32i_defs_OperandSize] <= 'd255;
		end
		else if (write_enable_3)
			mem[addr_3 * rv32i_defs_OperandSize+:rv32i_defs_OperandSize] <= write_data_3;
endmodule
module main_decoder (
	opcode,
	branch,
	jump,
	result_src,
	mem_write,
	alu_src,
	imm_src,
	reg_write,
	alu_op
);
	input wire [6:0] opcode;
	output reg branch;
	output reg jump;
	output reg [1:0] result_src;
	output reg mem_write;
	output reg alu_src;
	output reg [1:0] imm_src;
	output reg reg_write;
	output reg [1:0] alu_op;
	wire [6:0] opcode_enum;
	assign opcode_enum = opcode;
	always @(*)
		case (opcode)
			7'b0000011: begin
				reg_write = 1;
				imm_src = 'b0;
				alu_src = 1;
				mem_write = 0;
				result_src = 'b1;
				branch = 0;
				alu_op = 'b0;
				jump = 0;
			end
			7'b0100011: begin
				reg_write = 0;
				imm_src = 'b1;
				alu_src = 1;
				mem_write = 1;
				result_src = 2'bx0;
				branch = 0;
				alu_op = 'b0;
				jump = 0;
			end
			7'b0110011: begin
				reg_write = 1;
				imm_src = 2'bxx;
				alu_src = 0;
				mem_write = 0;
				result_src = 'b0;
				branch = 0;
				alu_op = 'b10;
				jump = 0;
			end
			7'b1100011: begin
				reg_write = 0;
				imm_src = 'b10;
				alu_src = 0;
				mem_write = 0;
				result_src = 2'bxx;
				branch = 1;
				alu_op = 'b1;
				jump = 0;
			end
			7'b0010011: begin
				reg_write = 1;
				imm_src = 'b0;
				alu_src = 1;
				mem_write = 0;
				result_src = 'b0;
				branch = 0;
				alu_op = 'b10;
				jump = 0;
			end
			7'b1101111: begin
				reg_write = 1;
				imm_src = 'b11;
				alu_src = 1'bx;
				mem_write = 0;
				result_src = 'b10;
				branch = 0;
				alu_op = 2'bxx;
				jump = 1;
			end
			default: begin
				reg_write = 'b0;
				imm_src = 2'bxx;
				alu_src = 1'bx;
				mem_write = 'b0;
				result_src = 'b0;
				branch = 'b0;
				alu_op = 2'bxx;
				jump = 'b0;
			end
		endcase
endmodule
module jump_control (
	jump,
	branch,
	branch_alu_neg,
	zero,
	pc_src
);
	input wire jump;
	input wire branch;
	input wire branch_alu_neg;
	input wire zero;
	output wire pc_src;
	wire alu_result;
	reg branch_result;
	assign alu_result = !zero;
	always @(*)
		case (branch_alu_neg)
			'd0: branch_result = alu_result;
			'd1: branch_result = !alu_result;
			default: branch_result = 1'bx;
		endcase
	assign pc_src = (branch & branch_result) | jump;
endmodule
module imm_extend (
	imm_src,
	instr,
	imm_ext
);
	input wire [1:0] imm_src;
	input wire [31:7] instr;
	output reg [31:0] imm_ext;
	always @(*)
		case (imm_src)
			'd0: imm_ext = {{20 {instr[31]}}, instr[31:20]};
			'd1: imm_ext = {{20 {instr[31]}}, instr[31:25], instr[11:7]};
			'd2: imm_ext = {{20 {instr[31]}}, instr[7], instr[30:25], instr[11:8], 1'b0};
			'd3: imm_ext = {{12 {instr[31]}}, instr[19:12], instr[20], instr[30:21], 1'b0};
			default: imm_ext = 'bx;
		endcase
endmodule
module control_unit (
	opcode,
	funct_3,
	funct_7,
	result_src,
	mem_write,
	alu_ctrl,
	alu_src,
	imm_src,
	reg_write,
	jump,
	branch,
	branch_alu_neg
);
	input wire [6:0] opcode;
	input wire [2:0] funct_3;
	input wire [6:0] funct_7;
	output wire [1:0] result_src;
	output wire mem_write;
	output wire [2:0] alu_ctrl;
	output wire alu_src;
	output wire [1:0] imm_src;
	output wire reg_write;
	output wire jump;
	output wire branch;
	output wire branch_alu_neg;
	wire [1:0] alu_op;
	main_decoder main_decoder(
		.opcode(opcode),
		.branch(branch),
		.jump(jump),
		.result_src(result_src),
		.mem_write(mem_write),
		.alu_src(alu_src),
		.imm_src(imm_src),
		.reg_write(reg_write),
		.alu_op(alu_op)
	);
	alu_decoder alu_decoder(
		.opcode_5(opcode[5]),
		.funct_3(funct_3),
		.funct_7_5(funct_7[5]),
		.alu_op(alu_op),
		.alu_ctrl(alu_ctrl),
		.branch_neg(branch_alu_neg)
	);
endmodule
module alu (
	a,
	b,
	operation,
	result,
	status
);
	localparam signed [31:0] rv32i_defs_OperandSize = 32;
	input wire [31:0] a;
	input wire [31:0] b;
	input wire [2:0] operation;
	output reg [31:0] result;
	output reg [3:0] status;
	reg n;
	reg z;
	reg c;
	reg v;
	always @(*) begin
		case (operation)
			3'b000: begin
				{c, result} = a + b;
				v = ((result[31] & !a[31]) & !b[31]) | ((!result[31] & a[31]) & b[31]);
			end
			3'b001: begin
				{c, result} = a - b;
				v = ((result[31] & !a[31]) & !b[31]) | ((!result[31] & a[31]) & !b[31]);
			end
			3'b011: begin
				result = a | b;
				c = 'b0;
				v = 'b0;
			end
			3'b010: begin
				result = a & b;
				c = 'b0;
				v = 'b0;
			end
			3'b101: begin
				result = {31'd0, a < b};
				c = 'b0;
				v = 'b0;
			end
			default: begin
				result = 'bx;
				c = 1'bx;
				v = 1'bx;
			end
		endcase
		n = result[31];
		z = result == {32 {1'sb0}};
		status = {n, z, c, v};
	end
endmodule

module alu_decoder (
	opcode_5,
	funct_3,
	funct_7_5,
	alu_op,
	alu_ctrl,
	branch_neg
);
	input wire opcode_5;
	input wire [2:0] funct_3;
	input wire funct_7_5;
	input wire [1:0] alu_op;
	output reg [2:0] alu_ctrl;
	output reg branch_neg;
	always @(*)
		casez ({alu_op, funct_3, opcode_5, funct_7_5})
			'b00zzzzz: begin
				alu_ctrl = 3'b000;
				branch_neg = 1'bx;
			end
			'b1000zz: begin
				alu_ctrl = 3'b001;
				branch_neg = 1'd1;
			end
			'b1100zz: begin
				alu_ctrl = 3'b101;
				branch_neg = 1'd0;
			end
			'b1101zz: begin
				alu_ctrl = 3'b101;
				branch_neg = 1'd1;
			end
			'b1000000: begin
				alu_ctrl = 3'b000;
				branch_neg = 1'bx;
			end
			'b1000001: begin
				alu_ctrl = 3'b000;
				branch_neg = 1'bx;
			end
			'b1000010: begin
				alu_ctrl = 3'b000;
				branch_neg = 1'bx;
			end
			'b1000011: begin
				alu_ctrl = 3'b001;
				branch_neg = 1'bx;
			end
			'b10010zz: begin
				alu_ctrl = 3'b101;
				branch_neg = 1'bx;
			end
			'b10110zz: begin
				alu_ctrl = 3'b011;
				branch_neg = 1'bx;
			end
			'b10111zz: begin
				alu_ctrl = 3'b010;
				branch_neg = 1'bx;
			end
			default: begin
				alu_ctrl = 3'bxxx;
				branch_neg = 1'bx;
			end
		endcase
endmodule

module clock_divider #(parameter N = 100)(
    clk,
    reset,
    divided_clk

    );

    input wire clk;
    input wire reset;
    output reg divided_clk; 
    
    reg [31:0] counter_value;
    
    always @(posedge clk)
        if(reset || counter_value == N)
            counter_value <= 0;
        else
            counter_value <= counter_value +1;
           
    always @(posedge clk)
    begin
        if(reset) divided_clk <= 0;
        else if(counter_value == N)
            divided_clk <= ~divided_clk;
        else
            divided_clk <= divided_clk;
    end
endmodule

module cpu_com_controller(
    clk,
    reset,
    rx,
    pc,
    tx,
    cpu_reset,
    cpu_run,
    uart_data,
    cmd_redy,
    cmd_send,
    instr_send,
    state
    );

    input wire clk;
    input wire reset;
    input wire rx;
    input wire [31:0] pc;
    output reg tx;
    output reg cpu_reset;
    output reg cpu_run;
    output reg [31:0] uart_data;
    output reg cmd_redy;
    output reg cmd_send;
    output reg instr_send;
    output reg [2:0] state;
    
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

module memory_com (
    clk,
    reset,
    rx,
    tx,
    write_enable,
    read_enable,
    mem_done,
    writeData,
    readData,
    address
);

   input wire clk;
   input wire reset;
   input wire rx;
   output wire tx;
   input  wire write_enable;
   input  wire read_enable;
   output reg  mem_done;
   input  wire [31:0] writeData;
   output reg  [31:0] readData;
   input  wire [31:0] address ; 

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


reg [31:0] readData_prev;
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

module PB_Debouncer_FSM#(
    parameter DELAY=10                 // Number of clock pulses to check stable button pressing
    )(
    clk,                 // base clock
	rst,                 // global reset
	PB,                  // raw asynchronous input from mechanical PB         
	PB_pressed_status,   // clean and synchronized pulse for button pressed
	PB_pressed_pulse,    // high if button is pressed
	PB_released_pulse    // clean and synchronized pulse for button released
    );

    input 	wire clk;                 // base clock
	input 	wire rst;                 // global reset
	input 	wire PB;                  // raw asynchronous input from mechanical PB         
	output 	reg PB_pressed_status;   // clean and synchronized pulse for button pressed
	output  reg PB_pressed_pulse;    // high if button is pressed
	output  reg PB_released_pulse;   // clean and synchronized pulse for button released
    
    reg    PB_sync_aux, PB_sync;

// Double flopping stage for synchronizing asynchronous PB input signal
// PB_sync is the synchronized signal
 always @(posedge clk) begin
     if (rst) begin
         PB_sync_aux <= 1'b0;
         PB_sync     <= 1'b0;
     end
     else begin
         PB_sync_aux <= PB;
         PB_sync     <= PB_sync_aux;
     end
 end
/////////////// FSM Description
	
	localparam DELAY_WIDTH = $clog2(DELAY);
	
	reg [DELAY_WIDTH-1:0]    delay_timer; 
    
    localparam  PB_IDLE = 'b000,
                PB_COUNT = 'b001,
                PB_PRESSED = 'b010,
                PB_STABLE = 'b011,
                PB_RELEASED = 'b100;

    reg [5:0] state;
    reg [5:0] next_state;

 //Timer keeps track of how many cycles the FSM remains in a given state
 //Automatically resets the counter "delay_timer" when changing state
  always @(posedge clk) begin
	if (rst) delay_timer <= 0;
	else if (state != next_state) delay_timer <= 0; //reset the timer when state changes
	else delay_timer <= delay_timer + 1;
  end


    // Combinational logic for FSM
    // Calcula hacia donde me debo mover en el siguiente ciclo de reloj basado en las entradas
    always @(*) begin
        //default assignments
        next_state          = PB_IDLE;
        PB_pressed_status   = 1'b0;
        PB_pressed_pulse    = 1'b0;
        PB_released_pulse   = 1'b0;
                
        case (state)
            PB_IDLE:        begin
                                if(PB_sync) begin   // si se inicia una operacion, empieza lectura de datos
                                    next_state= PB_COUNT;
                                end
                            end

            PB_COUNT:       begin
                                // Verifica si el timer alcanzo el valor predeterminado para este estado
                                if ((PB_sync && (delay_timer >= DELAY-1))) begin
                                    next_state = PB_PRESSED;
                                end 
                                else if (PB_sync)
                                    next_state = PB_COUNT;
                            end
                         
             PB_PRESSED:    begin
                                PB_pressed_pulse = 1'b1;
                                if (PB_sync)
                                    next_state = PB_STABLE;
                            end
             
             PB_STABLE:     begin
                                PB_pressed_status=1'b1;
                                next_state = PB_STABLE;
                         
                                if (~PB_sync)
                                    next_state = PB_RELEASED;
                            end

              PB_RELEASED:  begin
                                PB_released_pulse = 1'b1;
                                next_state = PB_IDLE;
                            end    
         endcase
    end    

    // sequential block for FSM. When clock ticks, update the state
    always @(negedge clk) begin
        if(rst) 
            state <= PB_IDLE;
        else 
            state <= next_state;
    end
    
endmodule


module uart_32bit_rx (
    clk,
    reset,
    rx,
    data_out,
    data_end
);
    input wire clk; 
    input wire reset;
    input wire rx;
    output reg [31:0] data_out;
    output reg data_end;

// UART Instance
reg [7:0] recv_data;
reg       recv_ready;

uart_sm_rx uart_rx (
    .clk      ( clk ),
    .reset    ( reset ),
    .rx       ( rx ),
    .byte_out ( recv_data ),
    .byte_end ( recv_ready )
);

// FSM States
localparam  IDLE       = 4'b0000,
            RECV_BYTE1 = 4'b0001,
            SAVE_BYTE1 = 4'b0010,
            RECV_BYTE2 = 4'b0011,
            SAVE_BYTE2 = 4'b0100,
            RECV_BYTE3 = 4'b0101,
            SAVE_BYTE3 = 4'b0110,
            RECV_BYTE4 = 4'b0111,
            SAVE_BYTE4 = 4'b1000,
            DONE       = 4'b1001;

reg [3:0] state;
reg [3:0] next_state ;  

always @(posedge clk) begin
    if(reset) begin
        state <= IDLE;
    end
    else begin
        state <= next_state;
    end
end

reg       rst_data;
reg       save;
reg [1:0] save_ctrl;

reg [2:0] i;

always @(posedge clk) begin
    if( reset || rst_data ) begin
        data_out <= 'b0;
    end
    else begin
        data_out <= data_out;
        if(save) begin
            for( i = 0; i <= 'b11; i=i+1'b1 ) begin
                if( save_ctrl == i[1:0] ) data_out[i*8+:8] <= recv_data;
            end
        end
    end
end

always @(*) begin
    next_state = IDLE;
    rst_data = 0;
    save = 0;
    save_ctrl = 0;
    data_end = 0;

    case(state)
        IDLE: begin
            rst_data = 1;
            next_state = RECV_BYTE1;
        end
        RECV_BYTE1: begin
            if( recv_ready ) next_state = SAVE_BYTE1;
            else next_state = RECV_BYTE1;
        end
        SAVE_BYTE1: begin
            save = 1;
            save_ctrl = 0;
            next_state = RECV_BYTE2;
        end
        RECV_BYTE2: begin
            if( recv_ready ) next_state = SAVE_BYTE2;
            else next_state = RECV_BYTE2;
        end
        SAVE_BYTE2: begin
            save = 1;
            save_ctrl = 1;
            next_state = RECV_BYTE3;
        end
        RECV_BYTE3: begin
            if( recv_ready ) next_state = SAVE_BYTE3;
            else next_state = RECV_BYTE3;
        end
        SAVE_BYTE3: begin
            save = 1;
            save_ctrl = 2;
            next_state = RECV_BYTE4;
        end
        RECV_BYTE4: begin
            if( recv_ready ) next_state = SAVE_BYTE4;
            else next_state = RECV_BYTE4;
        end
        SAVE_BYTE4: begin
            save = 1;
            save_ctrl = 3;
            next_state = DONE;
        end
        DONE: begin
            data_end = 1;
            next_state = IDLE;
        end
    endcase
end

endmodule


module uart_32bit_tx(
    clk,
    reset,
    send_start,
    data_in,
    tx,
    data_end
);
input wire clk;
input wire reset;
input wire send_start;
input wire [31:0] data_in;
output reg tx;
output reg data_end;

// UART Instances
reg        byte_start;
reg [7:0]  send_data;
reg        send_ready;

uart_sm_tx uart_tx(
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

module uart_sm_rx(
    clk,
    reset,
    rx,
    byte_out,
    byte_end
    );

    input wire clk; 
    input wire reset;
    input wire rx;
    output reg [7:0] byte_out;
    output reg byte_end;
    
    //cycles count ---------------------------------------------------------------------------------------------------------------------
   
    reg [4:0] count;
    reg [4:0] pre_count;
    
    always @(posedge clk) begin
        if(reset) begin
            count <= 0;
        end
        else count <= pre_count;
    end
    
    //bit count -----------------------------------------------------------------------------------------------------------------------
    
    reg [3:0] bit_count;
    reg [3:0] pre_bit_count;
    
    always @(posedge clk) begin
        if(reset) bit_count <= 0;
        else bit_count <= pre_bit_count;
    end
    
    //byte out -----------------------------------------------------------------------------------------------------------------------
    
    reg [7:0] pre_byte_out;
    
    always @(posedge clk) begin
        if(reset) byte_out <= 0;
        else byte_out <= pre_byte_out;
    end
    
    //state machine ---------------------------------------------------------------------------------------------------------------------
    
    reg [1:0] state;
    reg [1:0] next_state;
    
    localparam IDLE = 0;
    localparam START = 1;
    localparam WAIT_FRONT = 2;
    localparam WAIT_BACK = 3;
    
    always @(posedge clk) begin
        if(reset) state <= IDLE;
        else state <= next_state;
    end
    
    always @(*) begin
        next_state = state;
        pre_count = count;
        pre_bit_count = bit_count;
        pre_byte_out = byte_out;
        byte_end = 0;
        case(state)
            IDLE: begin
                next_state = START;
            end
            
            START: begin
                if(rx==0) begin
                    next_state = WAIT_FRONT;
                    pre_bit_count = 0;
                end
            end
            
            WAIT_FRONT: begin
                pre_count = count + 1;
                if(count==15) begin
                    pre_bit_count = bit_count + 1; 
                    pre_count = 0;
                    next_state = WAIT_BACK;
                    case(bit_count)
                        1: pre_byte_out[0] = rx;
                        2: pre_byte_out[1] = rx;
                        3: pre_byte_out[2] = rx;
                        4: pre_byte_out[3] = rx;
                        5: pre_byte_out[4] = rx;
                        6: pre_byte_out[5] = rx;
                        7: pre_byte_out[6] = rx;
                        8: pre_byte_out[7] = rx;
                        9: begin
                            next_state = IDLE;
                            byte_end = 1;
                        end
                    endcase
                end
            end
            
            WAIT_BACK: begin
                pre_count = count + 1;
                if(count==15) begin
                    next_state = WAIT_FRONT;
                    pre_count = 0;
                end
            end
        endcase
    end
endmodule

module uart_sm_tx(
    clk,
    reset,
    send_pulse,
    byte_in,
    tx,
    byte_end
);

input wire clk;
input wire reset;
input wire send_pulse;
input wire [7:0] byte_in;
output reg tx;
output reg byte_end;
    
    //Tx --------------------------------------------------------------------------------------------------
    
    reg pre_tx;
    
    always @(posedge clk) begin
        if(reset) tx <= 1;
        else tx <= pre_tx;
    end
    
    //cycles count --------------------------------------------------------------------------------------------------
    
    reg [4:0] count;
    reg [4:0] pre_count;
    
    always @(posedge clk) begin
        if(reset) count <= 0;
        else count <= pre_count;
    end
    
    //bit count --------------------------------------------------------------------------------------------------
    
    reg [3:0] bit_count;
    reg [3:0] pre_bit_count;
    
    always @(posedge clk) begin
        if(reset) bit_count <= 0;
        else bit_count <= pre_bit_count;
    end
    
    // STATE MACHINE %%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
    
    localparam IDLE = 0;
    localparam SEND = 1;
    localparam WAITB = 2;
    
    reg [1:0] state;
    reg [1:0] next_state;
    
    always @(posedge clk) begin
        if(reset) state<= IDLE;
        else state <= next_state;
    end
    
    always @(*) begin
        next_state = state;
        pre_count = count;
        pre_bit_count = bit_count;
        pre_tx = tx;
        byte_end = 0;
        case(state)
            IDLE: begin
                pre_tx = 1;
                if(send_pulse == 1) begin
                    pre_bit_count = 0;
                    pre_count = 0;
                    next_state = SEND;
                end
            end
            
            SEND: begin
                pre_count = count + 1;
                if(count == 31) begin
                    pre_bit_count = bit_count + 1;
                    pre_count = 0;
                end
                case(bit_count)
                    0: begin
                        pre_tx = 0;
                    end
                    1: begin
                        pre_tx = byte_in[0];
                    end
                    2: begin
                        pre_tx = byte_in[1];
                    end
                    3: begin
                        pre_tx = byte_in[2];
                    end
                    4: begin
                        pre_tx = byte_in[3];
                    end
                    5: begin
                        pre_tx = byte_in[4];
                    end
                    6: begin
                        pre_tx = byte_in[5];
                    end
                    7: begin
                        pre_tx = byte_in[6];
                    end
                    8: begin
                        pre_tx = byte_in[7];
                    end
                    9: begin
                        pre_tx = 1;
                    end
                    10: begin
                        next_state = IDLE;
                        byte_end = 1;
                    end
                endcase
            end
        endcase
    end
endmodule

module word_32_bit_uart_rx(
    clk,
    reset,
    rx,
    instr,
    word_end
    );

    input wire clk;
    input wire reset;
    input wire rx;
    output reg [31:0] instr;
    output reg word_end;
    
    //byte in -------------------------------------------------------------------------------------------------
    
    wire [7:0] byte_in;
    wire byte_end;
    
    uart_sm_rx byte_rx(clk,reset,rx,byte_in,byte_end);
    
    //instr ----------------------------------------------------------------------------------------------------
    
    reg [31:0] pre_instr;
    
    always @(posedge clk) begin
        if(reset) instr <= 0;
        else instr <= pre_instr;
    end
    
    // state machine ----------------------------------------------------------------------------------------------------
    
    localparam WAITB1 = 0;
    localparam BYTE1 = 1;
    localparam WAITB2 = 2;
    localparam BYTE2 = 3;
    localparam WAITB3 = 4;
    localparam BYTE3 = 5;
    localparam WAITB4 = 6;
    localparam BYTE4 = 7;
    localparam WAIT_END = 8;
    localparam CMD = 9;
    localparam CMD_END = 10;
    
    reg [3:0] state;
    reg [3:0] next_state;
    
    always @(posedge clk) begin
        if(reset) state <= WAITB1;
        else state <= next_state;
    end
    
    always @(*) begin
        next_state =  state;
        pre_instr = instr;
        word_end = 0;
        case(state)
            WAITB1: begin
                word_end = 0;
                if(byte_in == 1) begin
                    if(byte_end) next_state = BYTE1;
                end 
                else if(byte_in == 0) begin
                    if(byte_end) next_state = CMD;
                end
            end
            
            CMD: begin
                if(byte_end) begin
                    word_end = 1;
                    next_state = CMD_END;
                end
                else begin
                    pre_instr[7:0] = byte_in;
                    pre_instr[31:8] = 0;
                end
            end
            
            CMD_END: begin
                word_end = 1;
                next_state = WAITB1;
            end
            
            BYTE1: begin
                if(byte_end) next_state = WAITB2;
                else pre_instr[7:0] = byte_in;
            end
            
            WAITB2: begin
                if(byte_in == 2) begin
                    if(byte_end) next_state = BYTE2;
                end
            end
            
            BYTE2: begin
                if(byte_end) next_state = WAITB3;
                else pre_instr[15:8] = byte_in;
            end
            
            WAITB3: begin
                if(byte_in == 3) begin
                    if(byte_end) next_state = BYTE3;
                end
            end
            
            BYTE3: begin
                if(byte_end) next_state = WAITB4;
                else pre_instr[23:16] = byte_in;
            end
            
            WAITB4: begin
                if(byte_in == 4) begin
                    if(byte_end) next_state = BYTE4;
                end
            end
            
            BYTE4: begin
                if(byte_end) begin
                    word_end = 1;
                    next_state = WAIT_END;
                end
                else pre_instr[31:24] = byte_in;
            end
            WAIT_END: begin
                word_end = 1;
                next_state = WAITB1;
            end
        endcase
    end
endmodule

module word_32bit_uart_tx(
    clk,
    reset,
    addr_query,
    addr,
    tx,
    word_send
    );

    input wire clk;
    input wire reset;
    input wire addr_query;
    input wire [31:0] addr;
    output wire tx;
    output reg word_send;
    
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
