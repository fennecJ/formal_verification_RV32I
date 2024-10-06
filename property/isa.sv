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
    return rv32i_decoded;
endfunction : decode

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

function static logic is_valid_E_inst(input logic [31:0] inst);
    return (inst[31:20] == 12'b0000_0000_000?) && (inst[19:7] == 0);
endfunction : is_valid_E_inst

function static logic is_validInst(input logic [31:0] inst);
    rv32i_inst_t rv32i;
    logic [9:0] funct_comb;

    rv32i = decode(inst);
    funct_comb = {rv32i.funct7, rv32i.funct3};

    case (rv32i.opcode)
        OPC_LUI: return 1'b1;
        OPC_AUIPC: return 1'b1;
        OPC_JAL: return 1'b1;
        OPC_JALR: return (rv32i.funct3 == 3'b000);
        OPC_B: return (rv32i.funct3 inside {BEQ, BNE, BLT, BGE, BLTU, BGEU});
        OPC_IL: return (funct_comb inside {LB, LH, LW, LBU, LHU});
        OPC_S: return (rv32i.funct3 inside {SB, SH, SW});
        OPC_I: return (funct_comb inside {ADDI, XORI, ORI, ANDI, SLLI, SRLI, SRAI, SLTI, SLTIU});
        OPC_R: return (funct_comb inside {ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND});
        OPC_FENCE: return (rv32i.funct3 == 3'b000);  // FENCE, FENCE.TSO, PAUSE
        OPC_E: return is_valid_E_inst(rv32i.inst);
        default: return 1'b0;
    endcase
endfunction

logic [31:0] if_inst;

module isa (
    input clk,
    input rst
);
    assign if_inst = core.if_unit.rv_instr;
    rv32i_inst_t rv32i;

    always_comb begin
        rv32i = decode(if_inst);
    end

    property CHECK_INST_VALID_ASSUME;
        @(posedge clk) disable iff (rst) if_inst[6:0] == 7'b0110111 ||  // LUI
        if_inst[6:0] == 7'b0010111 ||  // AUIPC
        if_inst[6:0] == 7'b1101111 ||  // JAL
        if_inst[6:0] == 7'b1100111 ||  // JALR

        (if_inst[6:0] == 7'b1100011  // B-type (Branch)
        && if_inst[14:12] != 3'b010 && if_inst[14:12] != 3'b011) ||
            (if_inst[6:0] == 7'b0000011  // L-type
        && if_inst[14:12] != 3'b011 && if_inst[14:12] != 3'b110 && if_inst[14:12] != 3'b111) ||
            (if_inst[6:0] == 7'b0100011  // S-type
        && (if_inst[14:12] == 3'b000 || if_inst[14:12] == 3'b001 || if_inst[14:12] == 3'b010)) ||
            (if_inst[6:0] == 7'b0010011  // I-type 1
        && if_inst[14:12] != 3'b001 && if_inst[14:12] != 3'b101) ||
            (if_inst[6:0] == 7'b0010011  // I-type 2 (logit shift)
        && if_inst[31:25] == 7'd000 && (if_inst[14:12] == 3'b001 || if_inst[14:12] == 3'b101)) ||
            (if_inst[6:0] == 7'b0010011  // I-type 3 (arith shift)
        && if_inst[31:25] == 7'b0100000 && if_inst[14:12] == 3'b101) ||
            (if_inst[6:0] == 7'b0110011  // R-type 1
        && if_inst[31:25] == 7'd000) || (if_inst[6:0] == 7'b0110011  // R-type 2
        && if_inst[31:25] == 7'b0100000 && (if_inst[14:12] == 3'b101 || if_inst[14:12] == 3'b000))
            || (if_inst[6:0] == 7'b0001111  // FENCE, FENCE.TSO, PAUSE
        && if_inst[14:12] == 3'b000) || (if_inst[6:0] == 7'b1110011  // ECALL, EBREAK
        && if_inst[19:7] == 13'b0 && (if_inst[31:20] == 12'd0 || if_inst[31:20] == 12'd1));
    endproperty

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
        @(posedge clk) disable iff (rst) 1 |-> 1;
    /* FIXME: */
    /* After Pipefollower is validated: */
    /* When the instruction in the WB stage is XORI, the value before the wb mux */
    /* should be imm ^ rs1. We can exploit function decode easily to get imm value */
    /* We can use a 32-bit temporary variable gold_xori to store this expected value. */
    endproperty : E2E_XORI_PRE_WB

    property E2E_XORI_RD;
        @(posedge clk) disable iff (rst) 1 |-> 1;
    /* FIXME: */
    /* After Pipefollower is validated: */
    /* When the instruction in the WB stage is XORI, */
    /* reg[rd] should equal the gold_xori value mentioned above. */
    endproperty : E2E_XORI_RD


    // FIXME:
    // For LB, we need check
    // 1. the req addr send to bus is the same as we calc
    // 2. wb_value_should be a proper value with mask
    // to shrink complexity, we can use stop and assume
    // to constraint all load result to be 0xabcd1234 and
    // check for addr end with 0, 1, 2, 3 to be [34, 12, cd, ab]
    // respectively

    // FIXME:
    // For BLT:
    // Add extra assume to ensure branch target is aligned to 4 (assume inst[8] = 0)
    // When the instruction in the WB staged is BLT, we examine if branch should be taken
    // Let taken_pc = WB's pc + simm13, non_taken_pc = WB's pc + 4
    // if taken |-> ##[1: $] inst's pc == taken_pc
    // else |-> ##[1: $] inst's pc == non_taken_pc (##[1: $] implies 1 or more cycle later)
    // we should consider stall, so the cycle to change pc may take more than 1

    // FIXME:
    // For JAL
    // Add extra assume to ensure branch target is aligned to 4 (assume inst[8] = 0)
    // When the instruction in the WB staged is JAL,
    // Let taken_pc = WB's pc + (simm20 << 1)
    // |->  ##[1: $] inst's pc == taken_pc
    // result to be write back should be WB's pc + 4
    // |->  ##[1: $] reg[rd] should be same as result

    // FIXME:
    // For AUIPC
    // When the instruction in the WB staged is AUIPC
    // Let result to be WB's pc + inst.uimm12
    // check following:
    // 1. wb_val == result
    // 2. |->  ##[1: $] reg[rd] should be same as result





`ifdef CheckInstValidAssume
    instValidCheck :
    assert property (CHECK_INST_VALID_ASSUME);
`endif  // CheckInstValidAssume

`ifdef RegFileStable
    /* FIXME: reg file's value should be stable in each cycle if it's not rd */
    // All check for reg[rd] can be simplify to be check rd_idx only
    // Once we prove reg file itself worked correctly
`endif  // RegFileStable

`ifdef PipeFollower
    /* FIXME: validate pipeline follower is follow the design correctly in each cycle */
    /* Check only IF/PD/ID/EX/MEM/WB */
    /* PipeFollower should also follow PC for Branch checking */
`endif  // PipeFollower



`ifdef ISA_GROUP_A
    /* FIXME: add other isa for group A [XORI, BLT, JAL, LB, AUIPC] */
`ifdef xori
    e2e_xori_rd :
    assert property (E2E_XORI_RD);
    e2e_xori_pre_wb :
    assert property (E2E_XORI_PRE_WB);
`endif  // xori
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
endmodule

bind riscv_top_ahb3lite isa isa_i (
    .clk(HCLK),
    .rst(~HRESETn)
);
