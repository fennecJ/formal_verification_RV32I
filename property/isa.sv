`include "../RV12/rtl/verilog/core/riscv_core.sv"
typedef enum logic [6:0] {
    OPC_R     = 7'b0110011,  // R type inst
    OPC_I     = 7'b0010011,  // ADDI, XORI, ORI, ANDI, SLLI, SRLI, SRAI, SLTI, SLTIU
    OPC_IL    = 7'b0000011,  // LB, LH, LW, LBU, LHU
    OPC_JALR  = 7'b1100111,  // JALR
    OPC_S     = 7'b0100011,  // SB, SH, SW
    OPC_B     = 7'b1100011,  // Branch inst
    OPC_JAL   = 7'b1101111,
    OPC_LUI   = 7'b0110111,
    OPC_AUIPC = 7'b0010111,
    OPC_FENCE = 7'b0001111,  // FENCE, FENCE.TSO, PAUSE
    OPC_E     = 7'b1110011   // ECALL, EBREAK
} opcode_t;

typedef struct packed {
    logic [31:0] inst;
    logic [6:0]  opcode;
    logic [4:0]  rd;
    logic [2:0]  funct3;
    logic [4:0]  rs1;
    logic [4:0]  rs2;
    logic [6:0]  funct7;
    logic [11:0] imm12_i;  // I-type 12bits imm
    logic [4:0]  imm5_i;   // I-type 5 bits imm (for shift)
    logic [11:0] imm12_s;  // S-type 12bits imm
    logic [20:0] imm21_j;  // J-type 21bits imm
    logic [12:0] imm13_b;  // B-type 13bits imm
    logic [19:0] uimm_20;  // lui/auipc 20bits uimm
    // FIXME: Add sign extended field if needed
} rv32i_inst_t;

// golden decode function
function static rv32i_inst_t decode(input logic [31:0] inst);
    rv32i_inst_t rv32i_decoded;
    rv32i_decoded.inst    = inst;
    rv32i_decoded.opcode  = inst[6:0];
    rv32i_decoded.rd      = inst[11:7];
    rv32i_decoded.funct3  = inst[14:12];
    rv32i_decoded.rs1     = inst[19:15];
    rv32i_decoded.rs2     = inst[24:20];
    rv32i_decoded.funct7  = inst[31:25];
    rv32i_decoded.imm12_i = inst[31:20];
    rv32i_decoded.imm5_i  = inst[24:20];
    rv32i_decoded.imm12_s = {inst[31:25], inst[11:7]};
    rv32i_decoded.imm21_j = {inst[31], inst[19:12], inst[20], inst[30:21], 1'b0};
    rv32i_decoded.imm13_b = {inst[31], inst[7], inst[30:25], inst[11:8], 1'b0};
    rv32i_decoded.uimm_20 = inst[31:12];
    return rv32i_decoded;
endfunction : decode

typedef struct packed {
    logic [31:0] inst;
    logic [31:0] pc;
} inst_pc_t;  // {inst, pc}

typedef struct packed {
    inst_pc_t inst_pc;  // {inst, pc}
    logic inst_valid;
    logic bubble;
} pipeline_info_t;

typedef enum logic [9:0] {  // {funct7, funct3}
    ADD  = {7'b0000000, 3'b000},
    SUB  = {7'b0100000, 3'b000},
    SLL  = {7'b0000000, 3'b001},
    SLT  = {7'b0000000, 3'b010},
    SLTU = {7'b0000000, 3'b011},
    XOR  = {7'b0000000, 3'b100},
    SRL  = {7'b0000000, 3'b101},
    SRA  = {7'b0100000, 3'b101},
    OR   = {7'b0000000, 3'b110},
    AND  = {7'b0000000, 3'b111}
} rtype_valid_funct_t;

typedef enum logic [9:0] {
    ADDI  = {7'b0000000, 3'b000},
    SLTI  = {7'b0000000, 3'b010},
    SLTIU = {7'b0000000, 3'b011},
    XORI  = {7'b0000000, 3'b100},
    ORI   = {7'b0000000, 3'b110},
    ANDI  = {7'b0000000, 3'b111},
    SLLI  = {7'b0000000, 3'b001},
    SRLI  = {7'b0000000, 3'b101},
    SRAI  = {7'b0100000, 3'b101}
} itype_valid_funct_t;

typedef enum logic [2:0] {
    LB  = 3'b000,
    LH  = 3'b001,
    LW  = 3'b010,
    LBU = 3'b100,
    LHU = 3'b101
} iltype_valid_funct3_t;

typedef enum logic [2:0] {
    // S type
    SB = 3'b000,
    SH = 3'b001,
    SW = 3'b010
} stype_valid_funct3_t;

typedef enum logic [2:0] {
    // B type
    BEQ  = 3'b000,
    BNE  = 3'b001,
    BLT  = 3'b100,
    BGE  = 3'b101,
    BLTU = 3'b110,
    BGEU = 3'b111
} btype_valid_funct3_t;

typedef enum logic [2:0] {
    // FENCE
    FENCE   = 3'b000,
    FENCE_I = 3'b001
} fence_valid_funct3_t;

function static logic is_valid_E_inst(input logic [31:0] inst);
    // inst[20] can be either 0 or 1, no need to constraint
    return (inst[31:21] == 11'b0000_0000_000) && (inst[19:7] == 0);
endfunction : is_valid_E_inst

function static logic is_valid_FENCE_inst(input logic [31:0] inst);
    casex (inst)
        32'b0000????????_00000_000_00000_0001111:  // FENCE.I
        return 1;
        32'b000000000000_00000_001_00000_0001111:  // FENCE
        return 1;
        default: return 0;
    endcase
endfunction : is_valid_FENCE_inst

function static logic is_validInst(input logic [31:0] inst);
    rv32i_inst_t rv32i;
    logic [9:0] funct_comb;

    rv32i = decode(inst);
    funct_comb = {rv32i.funct7, rv32i.funct3};

    case (rv32i.opcode)
        OPC_LUI: return 1'b1;
        OPC_AUIPC: return 1'b1;
        OPC_JAL: return (rv32i.imm21_j[1:0] == 2'b0);
        OPC_JALR: return ((rv32i.funct3 == 3'b000) && (rv32i.imm12_i[1:0] == 2'h0));
        OPC_B:
        return ((rv32i.funct3 inside {BEQ, BNE, BLT, BGE, BLTU, BGEU} &&
                 (rv32i.imm13_b[1:0] == 2'h0)));
        OPC_IL: return (funct_comb inside {LB, LH, LW, LBU, LHU});
        OPC_S: return (rv32i.funct3 inside {SB, SH, SW});
        OPC_I: return (funct_comb inside {ADDI, XORI, ORI, ANDI, SLLI, SRLI, SRAI, SLTI, SLTIU});
        OPC_R: return (funct_comb inside {ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND});
        OPC_FENCE: return is_valid_FENCE_inst(rv32i.inst);  // FENCE
        OPC_E: return is_valid_E_inst(rv32i.inst);
        default: return 1'b0;
    endcase
endfunction

logic [31:0] if_inst;
logic [31:0] if_pc;

rv32i_inst_t wb_inst_dc;
rv32i_inst_t mem_inst_dc;

//pipeline follower

localparam logic [31:0] NOP = 32'h13;
localparam logic [31:0] PC_INIT = 'h200;


//inst info

logic if_flush;
logic pd_flush;
logic id_flush;
logic ex_flush;
logic wb_flush;

//wires for some bubble use reg+wire to implement(ex : id_inst.bubble)
logic id_bubble_cond;
logic id_bubble_r;

//flushes core
logic core_pd_flush;
logic core_bu_flush;
logic core_bu_cacheflush;

//stalls core
logic core_id_stall;
logic core_pd_stall;
logic core_ex_stall;
logic core_mem_stall[2];
logic core_wb_stall;

logic wb_stall_past;

module isa (
    input clk,
    input rst
);
    rv32i_inst_t if_inst_dc;
    rv32i_inst_t id_inst_dc;
    pipeline_info_t if_pipeline_info;
    pipeline_info_t pd_pipeline_info;
    pipeline_info_t id_pipeline_info;
    pipeline_info_t ex_pipeline_info;
    pipeline_info_t mem_pipeline_info;
    pipeline_info_t wb_pipeline_info;

    logic ex_bubble_misc;
    logic ex_inst_valid;  // inst valid signal propagated from ex stage

    always_comb begin
        if_inst_dc = decode(if_pipeline_info.inst_pc.inst);
        id_inst_dc = decode(id_pipeline_info.inst_pc.inst);
    end

    logic id_valid_inst;
    assign id_valid_inst = is_validInst(id_pipeline_info.inst_pc.inst);

    always_ff @(posedge clk) begin
        if (rst) ex_bubble_misc <= 1'b1;
        else if (!core_ex_stall) ex_bubble_misc <= id_pipeline_info.bubble;
        // 0 means valid here (no bubble)
        // only when (there is no bubble from id) and (inst from id is valid) then we can set to valid (0)
        // However, we have assumed that all inst should be validInst, thus there is no need for checking
        // if inst valid. Original logic is
        // ex_bubble_misc <= (!id_pipeline_info.bubble && is_validInst(id_pipeline_info.inst_pc.inst)) ? 1'b0 : 1'b1;
        // Which can be simply to ex_bubble_misc <= id_pipeline_info.bubble; when is_validInst is always hold.
    end

    assign if_inst = core.if_unit.rv_instr;  //! use imem_parcel_i instead?

    // Directly follow the logic in core.if_unit

    always_comb begin
        if (rst) if_pc = PC_INIT;
        // if_pc will never be du_dato_i (with assume no_dbg_change_pc)
        else if (core.if_unit.du_we_pc_strb) if_pc = core.if_unit.du_dato_i;
        else if (!core.if_unit.pd_stall_i && !core.if_unit.du_stall_i) begin
            if_pc = core.if_unit.if_nxt_pc_o;
        end else if_pc = core.if_unit.if_pc_o;  // remain unchanged
    end
    rv32i_inst_t rv32i;

    always_comb begin
        rv32i = decode(if_inst);
    end

    always_comb begin
        wb_inst_dc  = decode(wb_pipeline_info.inst_pc.inst);
        mem_inst_dc = decode(mem_pipeline_info.inst_pc.inst);
    end

    //helper signal in write back stage
    logic [31:0] wb_rs1;
    logic [31:0] wb_rs2;
    assign wb_rs1 = (|(wb_inst_dc.rs1)) ? (core.int_rf.rf[wb_inst_dc.rs1]) : 0;
    assign wb_rs2 = (|(wb_inst_dc.rs2)) ? (core.int_rf.rf[wb_inst_dc.rs2]) : 0;

    // xori
    logic [31:0] xori_result;
    assign xori_result = (wb_rs1) ^ ({20'h0, wb_inst_dc.imm12_i});
    logic xori_trigger;
    assign xori_trigger = ((wb_inst_dc.opcode == OPC_I) && (wb_inst_dc.funct3 == XORI)) &&
        wb_pipeline_info.inst_valid;

    // LB
    logic lb_trigger;
    logic [31:0] lb_gold_data[4];
    logic [31:0] last_mem_addr;

    always_ff @(posedge clk) begin
        lb_gold_data[0] <= {{24{core.dmem_q_i[7]}}, core.dmem_q_i[7:0]};
        lb_gold_data[1] <= {{24{core.dmem_q_i[15]}}, core.dmem_q_i[15:8]};
        lb_gold_data[2] <= {{24{core.dmem_q_i[23]}}, core.dmem_q_i[23:16]};
        lb_gold_data[3] <= {{24{core.dmem_q_i[31]}}, core.dmem_q_i[31:24]};
        last_mem_addr   <= core.wb_unit.mem_memadr_i;
    end

    logic [31:0] lb_gold_addr;
    assign lb_trigger = ((wb_inst_dc.opcode == OPC_IL)) && ((wb_inst_dc.funct3 == LB)) &&
        wb_pipeline_info.inst_valid;
    assign lb_gold_addr = {{20{wb_inst_dc.imm12_i[11]}}, wb_inst_dc.imm12_i} + wb_rs1;

    // BLT
    logic blt_trigger;
    logic [31:0] blt_non_taken_addr;
    logic [31:0] blt_taken_addr;
    logic [31:0] blt_gold_addr;
    logic blt_taken;
    logic had_blt_past;
    logic valid_blt;
    assign valid_blt = (wb_inst_dc.opcode == OPC_B) && (wb_inst_dc.funct3 == BLT) &&
        wb_pipeline_info.inst_valid;

    always_ff @(posedge clk) begin
        if (rst) had_blt_past <= 1'b0;
        else if (valid_blt) had_blt_past <= 1'b1;
        else if (blt_trigger && !valid_blt)  // pull down BLT rec when blt triggered
            had_blt_past <= 1'b0;
    end

    assign blt_taken = $signed(wb_rs1) < $signed(wb_rs2);
    assign blt_trigger = had_blt_past && wb_pipeline_info.inst_valid;
    assign blt_non_taken_addr = wb_pipeline_info.inst_pc.pc + 32'd4;
    assign blt_taken_addr = wb_pipeline_info.inst_pc.pc +
        {{19{wb_inst_dc.imm13_b[12]}}, wb_inst_dc.imm13_b};
    always_ff @(posedge clk) begin
        if (valid_blt) blt_gold_addr <= blt_taken ? blt_taken_addr : blt_non_taken_addr;
    end

    // JAL

    // AUIPC
    logic auipc_trigger;
    logic [31:0] auipc_uimm;
    logic [31:0] auipc_gold_res;
    assign auipc_uimm = {wb_inst_dc.uimm_20, 12'b0};
    assign auipc_gold_res = auipc_uimm + wb_pipeline_info.inst_pc.pc;
    assign auipc_trigger = (wb_inst_dc.opcode == OPC_AUIPC) && wb_pipeline_info.inst_valid;

    // stall and flush
    always_comb begin
        core_pd_flush = core.pd_flush;
        core_bu_flush = core.bu_flush;
        core_bu_cacheflush = core.bu_cacheflush;

        core_id_stall = core.id_stall;
        core_pd_stall = core.pd_stall;
        core_ex_stall = core.ex_stall;
        core_mem_stall = core.mem_stall;
        core_wb_stall = core.wb_stall;
    end

    always_ff @(posedge clk) begin
        wb_stall_past <= core_wb_stall;
    end


    //pipeline follower
    // imem to if
    always_comb begin
        if_flush = core_pd_flush;  //ignore parcel valid(no compressed inst)
    end
    always_ff @(posedge clk) begin
        if_pipeline_info.inst_valid <= 1'b0;
        if (rst) if_pipeline_info.inst_pc <= {NOP, PC_INIT};
        else if (!core_pd_stall) if_pipeline_info.inst_pc <= {if_inst, if_pc};  //ignore WFI
    end

    always_ff @(posedge clk) begin
        if (rst) if_pipeline_info.bubble <= 1;
        else if (if_flush) if_pipeline_info.bubble <= 1;
        else if (!core_pd_stall) if_pipeline_info.bubble <= core.pd_latch_nxt_pc;  //ignore WFI
    end
    // if to pd
    always_comb begin
        pd_flush = core_bu_flush;  // branch unit /state control
    end
    always_ff @(posedge clk) begin
        pd_pipeline_info.inst_valid <= 1'b0;
        if (rst) pd_pipeline_info.inst_pc <= {NOP, PC_INIT};
        else if (!core_id_stall) pd_pipeline_info.inst_pc <= if_pipeline_info.inst_pc;
    end

    always_ff @(posedge clk) begin
        if (rst) pd_pipeline_info.bubble <= 1;
        else if (pd_flush) pd_pipeline_info.bubble <= 1;
        else if (!core_id_stall) pd_pipeline_info.bubble <= if_pipeline_info.bubble;
    end
    // pd to id
    always_comb begin
        id_flush = core_bu_flush;  // branch unit /state control
    end
    always_comb begin : id_bubble_wire
        id_bubble_cond = core_ex_stall | core_bu_flush;
    end
    always_ff @(posedge clk) begin
        id_pipeline_info.inst_valid <= 1'b0;
        if (rst) id_pipeline_info.inst_pc <= {NOP, PC_INIT};
        else if (!core_ex_stall) id_pipeline_info.inst_pc <= pd_pipeline_info.inst_pc;
    end
    always_ff @(posedge clk) begin
        if (rst) id_bubble_r <= 1;
        else if (core_bu_flush) id_bubble_r <= 1;
        // should rewrite core_id_stall(signal for dependency checking)?
        else if (!core_ex_stall) id_bubble_r <= pd_pipeline_info.bubble | core_id_stall;
    end
    always_comb begin
        id_pipeline_info.bubble = id_bubble_r | id_bubble_cond;
    end
    // id to ex
    always_comb begin
        ex_flush = core_bu_flush;  // branch unit /state control
    end
    always_ff @(posedge clk) begin
        if (rst) ex_pipeline_info.inst_pc <= {NOP, PC_INIT};
        else if (!core_ex_stall) ex_pipeline_info.inst_pc <= id_pipeline_info.inst_pc;
    end
    always_comb @(posedge clk) begin
        ex_pipeline_info.bubble = (core.ex_units.alu_bubble) && (core.ex_units.lsu_bubble) &&
            (core.ex_units.mul_bubble) && (core.ex_units.div_bubble);
        // Because we assume that all inst is valid, if last id's inst has no bubble
        // Then it must be valid inst in exe stage
        ex_inst_valid = ~(ex_pipeline_info.bubble & ex_bubble_misc);
        ex_pipeline_info.inst_valid = ex_inst_valid;
    end
    // ex to mem
    always_ff @(posedge clk) begin
        if (rst) begin
            mem_pipeline_info.inst_pc <= {NOP, PC_INIT};
            mem_pipeline_info.inst_valid <= 1'b0;
        end else if (!core_wb_stall) begin
            mem_pipeline_info.inst_pc <= ex_pipeline_info.inst_pc;
            mem_pipeline_info.inst_valid <= ex_pipeline_info.inst_valid;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) mem_pipeline_info.bubble <= 1;
        else if (!core_wb_stall) mem_pipeline_info.bubble <= ex_pipeline_info.bubble;
    end
    // mem to wb
    always_comb begin
        wb_flush = core_bu_flush;  // branch unit /state control
    end
    always_ff @(posedge clk) begin
        if (rst) begin
            wb_pipeline_info.inst_pc <= {NOP, PC_INIT};
        end else if (!core_wb_stall) begin
            wb_pipeline_info.inst_pc <= mem_pipeline_info.inst_pc;
        end
    end

    always_ff @(posedge clk) begin
        if (rst) wb_pipeline_info.inst_valid <= 1'b0;
        else if (core_wb_stall) wb_pipeline_info.inst_valid <= 1'b0;
        else wb_pipeline_info.inst_valid <= mem_pipeline_info.inst_valid;
    end

    always_ff @(posedge clk) begin
        if (rst) wb_pipeline_info.bubble <= 1;
        else if (!core_wb_stall) wb_pipeline_info.bubble <= mem_pipeline_info.bubble;
    end

    //assertion
    property CHECK_PIPE_IF_TO_PD;
        @(posedge clk) disable iff (rst) (if_pipeline_info.inst_pc.inst == core.if_insn.instr) &&
            (if_pipeline_info.bubble == core.if_insn.bubble);
    endproperty

    property CHECK_PIPE_PD_TO_ID;
        @(posedge clk) disable iff (rst) (pd_pipeline_info.inst_pc.inst == core.pd_insn.instr) &&
            (pd_pipeline_info.bubble == core.pd_insn.bubble);
    endproperty

    property CHECK_PIPE_ID_TO_EX;
        @(posedge clk) disable iff (rst) (id_pipeline_info.inst_pc.inst == core.id_insn.instr) &&
            (id_pipeline_info.bubble == core.id_insn.bubble);
    endproperty

    property CHECK_PIPE_EX_TO_MEM;
        @(posedge clk) disable iff (rst) (ex_pipeline_info.inst_pc.inst == core.ex_insn.instr) &&
            (ex_pipeline_info.bubble == core.ex_insn.bubble);
    endproperty

    property CHECK_PIPE_MEM_TO_WB;
        @(posedge clk) disable iff (rst) (mem_pipeline_info.inst_pc.inst == core.mem_insn[0].instr)
            && (mem_pipeline_info.bubble == core.mem_insn[0].bubble);
    endproperty

    property CHECK_PIPE_WB_TO_REG;
        @(posedge clk) disable iff (rst) (wb_pipeline_info.inst_pc.inst == core.wb_insn.instr) &&
            (wb_pipeline_info.bubble == core.wb_insn.bubble);
    endproperty

    // verilog_format: off
    property CHECK_INST_VALID_ASSUME;
        @(posedge clk) disable iff (rst)
        if_inst[6:0] == 7'b0110111 ||  // LUI
        if_inst[6:0] == 7'b0010111 ||  // AUIPC
        if_inst[6:0] == 7'b1101111 ||  // JAL
        if_inst[6:0] == 7'b1100111 ||  // JALR
        // B-type (Branch)
        (if_inst[6:0] == 7'b1100011 && if_inst[14:12] != 3'b010
        && if_inst[14:12] != 3'b011 && if_inst[8] == 1'h0) ||
        // L-type
        (if_inst[6:0] == 7'b0000011 && if_inst[14:12] != 3'b011
        && if_inst[14:12] != 3'b110 && if_inst[14:12] != 3'b111) ||
        // S-type
        (if_inst[6:0] == 7'b0100011
        && (if_inst[14:12] == 3'b000 || if_inst[14:12] == 3'b001 || if_inst[14:12] == 3'b010)) ||
        // I-type 1
        (if_inst[6:0] == 7'b0010011 && if_inst[14:12] != 3'b001 && if_inst[14:12] != 3'b101) ||
        // I-type 2 (logit shift)
        (if_inst[6:0] == 7'b0010011 && if_inst[31:25] == 7'd000
        && (if_inst[14:12] == 3'b001 || if_inst[14:12] == 3'b101)) ||
        // I-type 3 (arith shift)
        (if_inst[6:0] == 7'b0010011 && if_inst[31:25] == 7'b0100000 && if_inst[14:12] == 3'b101) ||
        // R-type 1
        (if_inst[6:0] == 7'b0110011 && if_inst[31:25] == 7'd000) ||
        // R-type 2
        (if_inst[6:0] == 7'b0110011 && if_inst[31:25] == 7'b0100000
        && (if_inst[14:12] == 3'b101 || if_inst[14:12] == 3'b000)) ||
        // FENCE
        // FENCE.I 32'b0000????????_00000_000_00000_0001111
        // FCENCE  32'b000000000000_00000_001_00000_0001111
        (if_inst[6:0] == 7'b0001111 && ({if_inst[31:28], if_inst[19:13], if_inst[11:7]} == 0)
        && (if_inst[12] == 0 || // FENCE.I
        (if_inst[12] == 1 && if_inst[27:20] == 0))) || // FCENCE
        // ECALL, EBREAK
        (if_inst[6:0] == 7'b1110011 && if_inst[19:7] == 13'b0
        && (if_inst[31:20] == 12'd0 || if_inst[31:20] == 12'd1));
    endproperty
    // verilog_format: on

    // Here, we have split the check for reg[rd] = rs1 ^ imm
    // into two independent properties. By doing this,
    // we reduce the overall complexity:
    // The original property reg[rd] = rs1 ^ imm has 3 degrees of freedom (rd, rs1, imm),
    // resulting in O(n^3) complexity. After the separation, the original
    // property is divided into two properties:
    // 1. The property E2E_XORI_PreRd checks if the result of imm ^ rs1 is correct,
    //    which has only 2 degrees of freedom (rs1, imm), leading to O(n^2) complexity.
    // 2. The property E2E_XORI_rd checks if reg[rd] equals the result, which has
    //    only 1 degree of freedom (rd), resulting in O(n) complexity.
    // Therefore, the overall complexity is reduced from O(n^3) to O(n^2).
    property E2E_XORI_PRE_WB;
        @(posedge clk) disable iff (rst) xori_trigger |-> (core.wb_r == (xori_result));
    endproperty : E2E_XORI_PRE_WB

    property E2E_XORI_RD;
        @(posedge clk) disable iff (rst) xori_trigger |-> (core.wb_dst == wb_inst_dc.rd);
    endproperty : E2E_XORI_RD

    property E2E_XORI_WE0;  // rd == 0 -> must disable write;
        @(posedge clk) disable iff (rst) xori_trigger && !(|wb_inst_dc.rd) |-> (!core.wb_we);
    endproperty : E2E_XORI_WE0

    property E2E_XORI_WE1;  // rd != 0 -> must enable write;
        @(posedge clk) disable iff (rst) xori_trigger && |wb_inst_dc.rd |-> (core.wb_we == 1);
    endproperty : E2E_XORI_WE1

    // For LB, we need check
    // 1. the req addr send to bus is the same as we calc
    // 2. wb_value_should be a proper value with mask
    // to shrink complexity, we can use stopat and assume
    // to constraint all load result to be 0xabcd1234 and
    // check for addr end with 0, 1, 2, 3 to be [34, 12, cd, ab]
    // respectively
    logic [31:0] tmp_adr;
    always_ff @(posedge clk) begin
        tmp_adr <= core.mem_memadr[0];
    end

    // check the riscv_wb.sv and you can see that wb result is determined by a register
    // wb_r_o, which is a determined in past cycle. And the sign_ext is also performed
    // in past cycle based on past cycle's mem_memadr_i. Thus when a lb_trigger is pulled
    // up, we should check past address instead of current address.
    // We assume that Dmem is ideal (That is, dmem has no stall). Thus any load/store instruction
    // enter wb must means that last_mem_addr must be inferred by current inst.
    property E2E_LB_ADDR;
        @(posedge clk) disable iff (rst) lb_trigger |-> last_mem_addr == lb_gold_addr;
    endproperty : E2E_LB_ADDR

    property E2E_LB_RES;
        @(posedge clk) disable iff (rst)
            lb_trigger |-> core.wb_r == lb_gold_data[lb_gold_addr[1:0]];
    endproperty : E2E_LB_RES

    property E2E_LB_RD;
        @(posedge clk) disable iff (rst) lb_trigger |-> (core.wb_dst == wb_inst_dc.rd);
    endproperty : E2E_LB_RD

    property E2E_LB_WE0;  // rd == 0 -> must disable write;
        @(posedge clk) disable iff (rst) lb_trigger && !(|wb_inst_dc.rd) |-> (!core.wb_we);
    endproperty : E2E_LB_WE0

    property E2E_LB_WE1;  // rd != 0 -> must enable write;
        @(posedge clk) disable iff (rst) lb_trigger && |wb_inst_dc.rd |-> (core.wb_we == 1);
    endproperty : E2E_LB_WE1

    // For BLT:
    // Add extra assume to ensure branch target is aligned to 4 (assume inst[8] = 0)
    // Let gold_pc = past BLT's pc + rs1 or + 4 (depends on taken or not)
    // blt_trigger:
    //  If there exist an valid inst with BLT in the past
    //  When next valid inst is enter wb staged
    // We check that the pc should be target gold_pc
    sequence blt_followed_by_invalid_inst_then_valid;
        valid_blt ##1
        // inst is not valid for 1~$(any numbers) consecutive cycles
        ((wb_pipeline_info.inst_valid == 0) [* 1: $])
        // then one cycle after, there is a valid inst
        ##1 wb_pipeline_info.inst_valid;
    endsequence : blt_followed_by_invalid_inst_then_valid

    sequence blt_followed_by_valid_inst_immediately;
        valid_blt ##1 wb_pipeline_info.inst_valid == 1;
    endsequence : blt_followed_by_valid_inst_immediately

    property E2E_BLT;
        // @(posedge clk) disable iff (rst) blt_trigger |-> core.wb_pc == blt_gold_addr;
        @(posedge clk) disable iff (rst) blt_followed_by_invalid_inst_then_valid or
            blt_followed_by_valid_inst_immediately |-> core.wb_pc == blt_gold_addr;
    endproperty : E2E_BLT

    // FIXME:
    // For JAL
    // Add extra assume to ensure branch target is aligned to 4 (assume inst[8] = 0)
    // When the instruction in the WB staged is JAL,
    // Let taken_pc = WB's pc + (simm20 << 1)
    // |->  ##[1: $] inst's pc == taken_pc
    // result to be write back should be WB's pc + 4
    // |->  ##[1: $] reg[rd] should be same as result

    // For AUIPC
    // When the instruction in the WB staged is AUIPC
    // Let result to be WB's pc + inst.uimm12
    // check following:
    // 1. wb_val == result
    // 2. |->  ##[1: $] reg[rd] should be same as result
    property E2E_AUIPC_PRE_WB;
        @(posedge clk) disable iff (rst) auipc_trigger |-> (core.wb_r == (auipc_gold_res));
    endproperty : E2E_AUIPC_PRE_WB

    property E2E_AUIPC_RD;
        @(posedge clk) disable iff (rst) auipc_trigger |-> (core.wb_dst == wb_inst_dc.rd);
    endproperty : E2E_AUIPC_RD

    property E2E_AUIPC_WE0;  // rd == 0 -> must disable write;
        @(posedge clk) disable iff (rst) auipc_trigger && !(|wb_inst_dc.rd) |-> (!core.wb_we);
    endproperty : E2E_AUIPC_WE0

    property E2E_AUIPC_WE1;  // rd != 0 -> must enable write;
        @(posedge clk) disable iff (rst) auipc_trigger && |wb_inst_dc.rd |-> (core.wb_we == 1);
    endproperty : E2E_AUIPC_WE1

    // invalid inst should never change reg file
    property INVALID_NO_WEN;
        @(posedge clk) disable iff (rst) wb_pipeline_info.inst_valid == 0 |-> core.wb_we == 0;
    endproperty : INVALID_NO_WEN

    logic valid_non_branch;
    logic [31:0] last_pc;
    assign valid_non_branch = (!(wb_inst_dc.opcode inside {OPC_JAL, OPC_JALR, OPC_B})) &&
        wb_pipeline_info.inst_valid;
    always_ff @(posedge clk) begin
        if (valid_non_branch) last_pc <= wb_pipeline_info.inst_pc.pc;
    end

    sequence non_branch_followed_by_invalid_then_valid;
        valid_non_branch ##1
        // inst is not valid for 1~$(any numbers) consecutive cycles
        ((wb_pipeline_info.inst_valid == 0) [* 1: $])
        // then one cycle after, there is a valid inst
        ##1 wb_pipeline_info.inst_valid == 1;
    endsequence : non_branch_followed_by_invalid_then_valid

    sequence non_branch_followed_by_valid_immediately;
        valid_non_branch ##1 wb_pipeline_info.inst_valid == 1;
    endsequence : non_branch_followed_by_valid_immediately

    // When there is no branch inst, next valid inst's pc should always incresed by 4
    property PC_INC4_WHEN_NO_BRANCH;
        @(posedge clk) disable iff (rst)
            non_branch_followed_by_invalid_then_valid or non_branch_followed_by_valid_immediately
            |-> wb_pipeline_info.inst_pc.pc == last_pc + 32'd4;
    endproperty : PC_INC4_WHEN_NO_BRANCH

`ifdef PC_INC4_NO_BRANCH
    pc_inc4_no_branch :
    assert property (PC_INC4_WHEN_NO_BRANCH);
`endif  // PC_INC4_NO_BRANCH

`ifdef CheckInstValidAssume
    instValidCheck :
    assert property (CHECK_INST_VALID_ASSUME);
`endif  // CheckInstValidAssume

`ifdef RegFileStable
    // Import necessary package
    import riscv_opcodes_pkg::rsd_t;

    // DUV's regfile signal
    logic [31:0] rf          [32];
    rsd_t        rf_src1_i;
    rsd_t        rf_src2_i;
    logic [31:0] rf_src1_q_o;
    logic [31:0] rf_src2_q_o;
    rsd_t        rf_dst_i;
    logic [31:0] rf_dst_d_i;
    logic        rf_we_i;
    logic        pd_stall_i;
    logic        id_stall_i;

    // Probe internal signal from DUV
    assign rf = core.int_rf.rf;
    assign rf_src1_i = core.int_rf.rf_src1_i;
    assign rf_src2_i = core.int_rf.rf_src2_i;
    assign rf_src1_q_o = core.int_rf.rf_src1_q_o;
    assign rf_src2_q_o = core.int_rf.rf_src2_q_o;
    assign rf_dst_i = core.int_rf.rf_dst_i;
    assign rf_dst_d_i = core.int_rf.rf_dst_d_i;
    assign rf_we_i = core.int_rf.rf_we_i;
    assign pd_stall_i = core.int_rf.pd_stall_i;
    assign id_stall_i = core.int_rf.id_stall_i;

    // Connect signals into assertion modules
    fv_regfile _fv_regfile (
        .clk(clk),
        .rst(rst),
        .rf(rf),
        .rf_src1_i(rf_src1_i),
        .rf_src2_i(rf_src2_i),
        .rf_src1_q_o(rf_src1_q_o),
        .rf_src2_q_o(rf_src2_q_o),
        .rf_dst_i(rf_dst_i),
        .rf_dst_d_i(rf_dst_d_i),
        .rf_we_i(rf_we_i),
        .pd_stall_i(pd_stall_i),
        .id_stall_i(id_stall_i)
    );
`endif  // RegFileStable

`ifdef PipeFollower
    IfToPd :
    assert property (CHECK_PIPE_IF_TO_PD);
    PdToId :
    assert property (CHECK_PIPE_PD_TO_ID);
    IdToEx :
    assert property (CHECK_PIPE_ID_TO_EX);
    ExToMem :
    assert property (CHECK_PIPE_EX_TO_MEM);
    MemToWb :
    assert property (CHECK_PIPE_MEM_TO_WB);
    WbToReg :
    assert property (CHECK_PIPE_WB_TO_REG);
`endif  // PipeFollower



`ifdef ISA_GROUP_A
    /* FIXME: add other isa for group A [XORI, BLT, JAL, LB, AUIPC] */
    invalid_no_wen :
    assert property (INVALID_NO_WEN);

    // Check if assumptions of Dmem still allow load insts to appear (should be covered)
    no_over_constraint_for_load :
    assert property (wb_pipeline_info.inst_valid && (wb_inst_dc.opcode == OPC_IL) |-> 1);

    // Check if assumptions of Dmem still allow store insts to appear (should be covered)
    no_over_constraint_for_store :
    assert property (wb_pipeline_info.inst_valid && (wb_inst_dc.opcode == OPC_S) |-> 1);

`ifdef xori
    e2e_xori_rd :
    assert property (E2E_XORI_RD);
    e2e_xori_pre_wb :
    assert property (E2E_XORI_PRE_WB);
    e2e_xori_we0 :
    assert property (E2E_XORI_WE0);
    e2e_xori_we1 :
    assert property (E2E_XORI_WE1);
`endif  // xori

`ifdef blt
    e2e_blt :
    assert property (E2E_BLT);
`endif  // blt

`ifdef auipc
    e2e_auipc_pre_wb :
    assert property (E2E_AUIPC_PRE_WB);

    e2e_auipc_rd :
    assert property (E2E_AUIPC_RD);

    e2e_auipc_we0 :
    assert property (E2E_AUIPC_WE0);

    e2e_auipc_we1 :
    assert property (E2E_AUIPC_WE1);
`endif  // auipc

`ifdef lb
    e2e_lb_addr :
    assert property (E2E_LB_ADDR);

    e2e_lb_res :
    assert property (E2E_LB_RES);

    e2e_lb_rd :
    assert property (E2E_LB_RD);

    e2e_lb_we0 :
    assert property (E2E_LB_WE0);

    e2e_lb_we1 :
    assert property (E2E_LB_WE1);
`endif  // lb

`endif  // ISA_GROUP_A


    property instValid;
        @(posedge clk) disable iff (rst) is_validInst(
            if_inst
        ) == 1'b1;
    endproperty

    instAlwaysValid :
    assume property (instValid);
    no_privilege_change_st_flush :
    assume property (##2 core.id_unit.st_flush_i == 0);

    // mask jalr source to prevent exception
    jalrSourceAlign :
    assume property (
        wb_inst_dc.opcode == OPC_JALR |-> wb_inst_dc.imm12_i[1:0] == 0 && wb_rs1[1:0] == 0);

    disableDmemErrStall :
    assume property ((core.dmem_err_i | core.dmem_misaligned_i | core.dmem_page_fault_i) == 0);

    noException :
    assume property ((core.if_exceptions.any | core.pd_exceptions.any | core.id_exceptions.any |
                      core.ex_exceptions.any | core.wb_exceptions.any) == 0);

    // The dmem and bus are black-boxed, so we can assume dmem responds immediately to requests.
    // Without black-boxing, stalls always occur after load/store due to the bus design (AHB3-Lite).
    // Our focus is verifying CPU correctness for a subset of RV32I, so bus handling is out of scope.
    // Key checks: CPU calculates correct imem/dmem addresses and handles fetched data properly.
    // CPU stalls, including those caused by memory access, are assumed correct, as verified by the
    // instructor and TAs under RV32I.
    idealDmem :
    assume property (@(posedge clk) disable iff (rst) core.dmem_ack_i == 1);

    pcAlign :
    assume property ((core.if_pc[1:0] | core.pd_pc[1:0] | core.id_pc[1:0] | core.ex_pc[1:0] |
                      core.mem_pc[0][1:0] | core.wb_pc[1:0]) == 2'b0);
    // no_dbg_change_pc : assume property (core.if_unit.du_we_pc_strb | core.if_unit.du_we_pc_i == 0);

    no_dbg_stall :
    assume property (core.dbg_stall_i == 0);

    always32bit_parcel :
    assume property (core.if_unit.is_16bit_instruction == 0);

endmodule

bind riscv_top_ahb3lite isa isa_i (
    .clk(HCLK),
    .rst(~HRESETn)
);
