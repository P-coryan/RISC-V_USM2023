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
	input reg mem_done;
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
