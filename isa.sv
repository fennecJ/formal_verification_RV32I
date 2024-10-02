`include "./RV12/rtl/verilog/core/riscv_core.sv"

typedef enum logic [6:0] {
    OPC_R    = 7'b0110011,
    OPC_I    = 7'b0010011, // ADDI, XORI, ORI, ANDI, SLLI, SRLI, SRAI, SLTI, SLTUI
    OPC_IL   = 7'b0000011, // LB, LH, LW, LBU, LHU
    OPC_IJ   = 7'b1100111, // JALR
    OPC_IE   = 7'b1110011, // ECALL, EBREAK
    OPC_S    = 7'b0100011,
    OPC_B    = 7'b1100011,
    OPC_J    = 7'b1101111,
    OPC_UL   = 7'b0110111,
    OPC_UAPC = 7'b0010111
} opcode_t;

typedef struct packed {
    logic [6:0]  opcode;
    logic [4:0]  rd;
    logic [2:0]  funct3;
    logic [4:0]  rs1;
    logic [4:0]  rs2;
    logic [6:0]  funct7;
    logic [11:0] imm12_i;  // I-type 12bits imm
    logic [4:0]  imm5_i;   // I-type 5 bits imm (for shift)
    logic [11:0] imm12_s;  // S-type 12bits imm
    logic [20:0] imm21_j;  // J-type 12bits imm
    logic [12:0] imm13_b;  // B-type 13bits imm
} rv32i_inst_t;

// golden decode function
function rv32i_inst_t decode(input logic [31:0] inst);
    rv32i_inst_t rv32i_decoded;
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

// FIXME: need be implemented with detailed fn7 fn3 value
typedef enum logic[9:0] { // {funct7, funct3}
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

typedef enum logic[9:0] {
    // I type
    ADDI  = {7'b0000000, 3'b000},
    SUBI  = {7'b0100000, 3'b000},
    SLLI  = {7'b0000000, 3'b001},
    SLTI  = {7'b0000000, 3'b010},
    SLTUI = {7'b0000000, 3'b011},
    XORI  = {7'b0000000, 3'b100},
    SRLI  = {7'b0000000, 3'b101},
    SRAI  = {7'b0100000, 3'b101},
    ORI   = {7'b0000000, 3'b110},
    ANDI  = {7'b0000000, 3'b111},
    // IL type
    LB,
    LH,
    LW,
    LBU,
    LHU,
    // IJ type
    JALR,
    // IE type
    ECALL,
    EBREAK
} itype_valid_funct_t;

typedef enum logic [2:0] {
    // S type
    SB = 3'b000,
    SH = 3'b001,
    SW = 3'b010
} stype_valid_funct_t;

typedef enum logic [2:0] {
    // B type
    BEQ,
    BNE,
    BLT,
    BGE,
    BLTU,
    BGEU
} btype_valid_funct_t;

typedef enum logic [2:0] {
    // J type
    JAL
} jtype_valid_funct_t;

typedef enum logic [2:0] {
    // UL type
    LUI
} ultype_valid_funct_t;

typedef enum logic [2:0] {
    // UAPC type
    AUIPC
} uapctype_valid_funct_t;

function logic is_validInst(input logic [31:0] inst);
    rv32i_inst_t rv32i;
    logic[9:0] funct_comb;

    rv32i = decode(inst);
    funct_comb = {rv32i.funct7, rv32i.funct3};

    case (rv32i.opcode)
        OPC_R   : return (funct_comb inside {ADD, SUB, SLL, SLT, SLTU, XOR, SRL, SRA, OR, AND});
        OPC_I   : return (funct_comb inside {ADDI, XORI, ORI, ANDI, SLLI, SRLI, SRAI, SLTI, SLTUI});
        OPC_IL  : return (funct_comb inside {LB, LH, LW, LBU, LHU});
        OPC_IJ  : return (funct_comb inside {JALR});
        OPC_IE  : return (funct_comb inside {ECALL, EBREAK});
        OPC_S   : return (rv32i.funct3 inside {SB, SH, SW});
        OPC_B   : return (rv32i.funct3 inside {BEQ, BNE, BLT, BGE, BLTU, BGEU});
        OPC_J   : return (rv32i.funct3 inside {JAL});
        OPC_UL  : return (rv32i.funct3 inside {LUI});
        OPC_UAPC: return (rv32i.funct3 inside {AUIPC});
        default: return 1'b0;
    endcase
endfunction


module isa (
    input clk,
    input rst
);
    

    property instValid;
        @(posedge clk) disable iff(rst)
        is_validInst(core.if_unit.rv_instr);
    endproperty
    instAlwaysValid: assume property (instValid);
endmodule

bind riscv_top_ahb3lite isa isa_i(
    .clk(HCLK),
    .rst(~HRESETn)
);

// stopat core.if_unit.rv_instr
// assume {is_validInst(core.if_unit.rv_instr)}