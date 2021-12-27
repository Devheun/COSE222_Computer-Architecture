//
//  Author: Prof. Taeweon Suh
//          Computer Science & Engineering
//          Korea University
//  Date: July 14, 2020
//  Description: Skeleton design of RV32I Single-cycle CPU
//

`timescale 1ns/1ns
`define simdelay 1

module rv32i_cpu (
            input         clk, reset,
            output [31:0] pc,              // program counter for instruction fetch
            input  [31:0] inst,          // incoming instruction
            output        Memwrite,    // 'memory write' control signal
            output [31:0] Memaddr,     // memory address 
            output [31:0] MemWdata,    // data to write to memory
            input  [31:0] MemRdata);    // data read from memory

  wire        auipc, lui;
  wire        alusrc, regwrite;
  wire [4:0]  alucontrol;
  wire        memtoreg, memwrite;
  wire        branch, jal, jalr;

//Start : for memread signal
  wire memread;
//End

// Start : for IF/ID FF
  wire  [31:0] IF_ID_inst;
//End
  //assign Memwrite = memwrite ;

  // Instantiate Controller
  controller i_controller(
      //Start : to connect the controller in cpu(input)
      .opcode      (IF_ID_inst[6:0]),
      .funct7      (IF_ID_inst[31:25]),
      .funct3      (IF_ID_inst[14:12]),
      //End
      //Start : to connect the controller in cpu(output)
      .memread   (memread),
      //End
      .auipc      (auipc),
      .lui         (lui),
      .memtoreg   (memtoreg),
      .memwrite   (memwrite),
      .branch      (branch),
      .alusrc      (alusrc),
      .regwrite   (regwrite),
      .jal         (jal),
      .jalr         (jalr),
      .alucontrol   (alucontrol));

  // Instantiate Datapath
  datapath i_datapath(
      .clk            (clk),
      .reset         (reset),
      .auipc         (auipc),
      .lui            (lui),
      .memtoreg      (memtoreg),
      .memwrite      (memwrite),
      .branch         (branch),
      .alusrc         (alusrc),
      .regwrite      (regwrite),
      .jal            (jal),
      .jalr            (jalr),
      .alucontrol      (alucontrol),
      .pc            (pc),
      .inst            (inst), 
      .MemWdata      (MemWdata),
      .MemRdata      (MemRdata),
      // Start : About EX_MEM F/F
      .EX_MEM_aluout      (Memaddr),
      .EX_MEM_memwrite   (Memwrite),
      // End
      //Start :
      .IF_ID_inst      (IF_ID_inst),
      //End
      // Start : memread control signal
      .memread      (memread));
      //end
      
endmodule


//
// Instruction Decoder 
// to generate control signals for datapath
//
module controller(input  [6:0] opcode,
                  input  [6:0] funct7,
                  input  [2:0] funct3,
                  output       auipc,
                  output       lui,
                  output       alusrc,
                  output [4:0] alucontrol,
                  output       branch,
                  output       jal,
                  output       jalr,
                  output       memtoreg,
                  output       memwrite,
                  output       regwrite,
       //Start
        output    memread);
      //End
   maindec i_maindec(
      .opcode      (opcode),
      .auipc      (auipc),
      .lui         (lui),
      .memtoreg   (memtoreg),
      .memwrite   (memwrite),
      .branch      (branch),
      .alusrc      (alusrc),
      .regwrite   (regwrite),
      .jal         (jal),
      .jalr         (jalr),
      //Start
      .memread   (memread));
      //End
   aludec i_aludec( 
      .opcode     (opcode),
      .funct7     (funct7),
      .funct3     (funct3),
      .alucontrol (alucontrol));


endmodule


//
// RV32I Opcode map = Inst[6:0]
//
`define OP_R         7'b0110011
`define OP_I_ARITH   7'b0010011
`define OP_I_LOAD     7'b0000011
`define OP_I_JALR     7'b1100111
`define OP_S         7'b0100011
`define OP_B         7'b1100011
`define OP_U_LUI      7'b0110111
`define OP_J_JAL      7'b1101111
//Start
`define OP_U_AUIPC      7'b0010111
//end

//
// Main decoder generates all control signals except alucontrol 
//
//
module maindec(input  [6:0] opcode,
               output       auipc,
               output       lui,
               output       regwrite,
               output       alusrc,
               output       memtoreg, memwrite,
               output       branch, 
               output       jal,
               output       jalr,
      //Start : to generate memread control signal
      output       memread);
      //End
//Start : Outputs are 10 (Before : reg [8:0] controls)
  reg [9:0] controls;
//End

  assign {auipc, lui, regwrite, alusrc, 
          memtoreg, memwrite, branch, jal, 
          jalr, memread} = controls;
          
  always @(*)
  begin
    case(opcode)
      `OP_R:          controls <= 10'b0010_0000_00; // R-type
      `OP_I_ARITH:    controls <= 10'b0011_0000_00; // I-type Arithmetic
      `OP_I_LOAD:    controls <= 10'b0011_1000_01; // I-type Load
      `OP_I_JALR:      controls <= 10'b0011_0000_10;
      `OP_S:          controls <= 10'b0001_0100_00; // S-type Store
      `OP_B:          controls <= 10'b0000_0010_00; // B-type Branch
      `OP_U_LUI:       controls <= 10'b0111_0000_00; // LUI
      `OP_J_JAL:       controls <= 10'b0011_0001_00; // JAL
 
      default:       controls <= 10'b0000_0000_00; // ???
    endcase
  end

endmodule

//
// ALU decoder generates ALU control signal (alucontrol)
//
module aludec(input      [6:0] opcode,
              input      [6:0] funct7,
              input      [2:0] funct3,
              output reg [4:0] alucontrol);

  always @(*)

    case(opcode)

      `OP_R:         // R-type
      begin
         case({funct7,funct3})
          10'b0000000_000: alucontrol <= 5'b00000; // addition (add)
          10'b0100000_000: alucontrol <=5'b10000; // subtraction (sub)
          10'b0000000_111: alucontrol <= 5'b00001; // and (and)
          10'b0000000_110: alucontrol <= 5'b00010; // or (or)
          default:         alucontrol <= 5'bxxxxx; // ???
        endcase
      end

      `OP_I_ARITH:   // I-type Arithmetic
      begin
         case(funct3)
          3'b000:  alucontrol <= 5'b00000; // addi (=add)
          3'b110:  alucontrol <= 5'b00010; // or (ori)
          3'b111:  alucontrol <= 5'b00001; // and (andi)
          3'b100:  alucontrol <= 5'b00011; // xori (=xor)
         //Start : to execute slli instruction
          3'b001:  alucontrol <= 5'b00100; // slli (=sll)
         //End
          default: alucontrol <= 5'bxxxxx; // ???
        endcase
      end

      `OP_I_LOAD:    // I-type Load (LW, LH, LB...)
         alucontrol <= 5'b00000;  // addition 

      `OP_B:         // B-type Branch (BEQ, BNE, ...)
         alucontrol <= 5'b10000;  // subtraction 
      `OP_I_JALR:
         alucontrol <=  5'b00000;
      `OP_S:         // S-type Store (SW, SH, SB)
         alucontrol <=  5'b00000;  // addition 

      `OP_U_LUI:       // U-type (LUI)
         alucontrol <=  5'b00000;  // addition
      

      default: 
         alucontrol <=  5'b00000;  // 

    endcase
    
endmodule


//
// CPU datapath
//
module datapath(input         clk, reset,
                input  [31:0] inst,
                input         auipc,
                input         lui,
                input         regwrite,
                input         memtoreg,
                input         memwrite,
                input         alusrc, 
                input  [4:0]  alucontrol,
                input         branch,
                input         jal,
                input         jalr,
      //Start: control signal datapath
      input         memread,
      //End
      
      //Start: From EX/MEM F/F
      output reg [31:0] EX_MEM_aluout,
      output reg EX_MEM_memwrite,
      //End
      //Start :
      output reg [31:0] IF_ID_inst,
      //End
                output reg [31:0] pc,
                //output [31:0] aluout,
                output [31:0] MemWdata,
                input  [31:0] MemRdata);

  wire [4:0]  rs1, rs2, rd;
  wire [2:0]  funct3;
  reg [31:0] rs1_data, rs2_data; //rs1_data, rs2_data require both reg and wire, so to solve this problem, I add rf_rs1_data, rf_rs2_data

  reg  [31:0] rd_data;
  wire [20:1] jal_imm;
  wire [31:0] se_jal_imm;
  wire [12:1] br_imm;
  wire [31:0] se_br_imm;
  wire [31:0] se_imm_itype;
  wire [31:0] se_imm_stype;
  wire [31:0] auipc_lui_imm;
  reg  [31:0] alusrc1;
  reg  [31:0] alusrc2;
  wire [31:0] branch_dest, jal_dest, jalr_dest, jalr_dest_tmp;
  wire        Nflag, Zflag, Cflag, Vflag;
  wire        f3beq, f3blt, f3bgeu;
  wire        beq_taken;
  wire        blt_taken;
  wire        bgeu_taken;
  wire        bne_taken;
  wire         f3bne;
  wire         f3bltu, bltu_taken;
  wire         f3bge, bge_taken;
  wire			btaken;

  wire			EX_MEM_Nflag,EX_MEM_Zflag,EX_MEM_Cflag,EX_MEM_Vflag;
  
  
  //Start : Each F/F PC
  reg[31:0] IF_ID_pc;
  reg[31:0] ID_EX_pc;
  reg[31:0] EX_MEM_pc;
  reg[31:0] MEM_WB_pc;
  //End
  
  //Start : variable stall and flush
  wire flush;
  reg stall;
  //End
  
  //Start : Original data path -> ID/EX data path
  reg[4:0] ID_EX_rs1;
  reg[4:0] ID_EX_rs2;
  reg[4:0] ID_EX_rd;
  reg[31:0] ID_EX_rs1_data;
  reg[31:0] ID_EX_rs2_data;
  reg[31:0] ID_EX_se_jal_imm;
  reg[31:0] ID_EX_se_br_imm;
  reg[31:0] ID_EX_se_imm_itype;
  reg[31:0] ID_EX_se_imm_stype;
  reg[31:0] ID_EX_auipc_lui_imm;

  reg[4:0] ID_EX_alucontrol;
  reg[2:0] ID_EX_funct3;
  reg ID_EX_alusrc;
  reg ID_EX_memwrite;
  reg ID_EX_branch;
  reg ID_EX_jal;
  reg ID_EX_jalr;
  reg ID_EX_auipc;
  reg ID_EX_lui;
  reg ID_EX_memread;
  reg ID_EX_regwrite;
  reg ID_EX_memtoreg;
  //End

  //Start : Original data path -> EX/MEM data path
  reg[31:0] EX_MEM_branch_dest;
  reg[31:0] EX_MEM_jal_dest;
  reg[31:0] EX_MEM_jalr_dest;
  reg[31:0] EX_MEM_jalr_dest_tmp;
  reg[31:0] EX_MEM_rs2_data;
  reg[4:0] EX_MEM_rd;
  
  reg EX_MEM_branch;
  reg EX_MEM_memtoreg;
  reg EX_MEM_regwrite;
  reg EX_MEM_jal;
  reg EX_MEM_jalr;
  reg EX_MEM_memread;
  //End

  //Start : Original data path -> MEM/WB data path
 reg[4:0] MEM_WB_rd;
 reg[31:0] MEM_WB_aluout;
 reg[31:0] MEM_WB_MemRdata;
 
 reg MEM_WB_regwrite;
 reg MEM_WB_memtoreg;
 reg MEM_WB_jal;
 reg MEM_WB_jalr;
 //End

 //Start : because of using both reg and wire, wire rs1_data -> wire rf_rs1_data
 wire [31:0] rf_rs1_data;
 wire [31:0] rf_rs2_data;
 wire [31:0] aluout;
 //End
  
  assign rs1 = IF_ID_inst[19:15];
  assign rs2 = IF_ID_inst[24:20];
  assign rd  = IF_ID_inst[11:7];
  assign funct3  = IF_ID_inst[14:12];


  //
  // PC (Program Counter) logic 
  //
  
  //Start : funct3
  assign f3beq  = (funct3 == 3'b000);
  assign f3blt  = (funct3 == 3'b100);
  assign f3bgeu = (funct3 == 3'b111);
  assign f3bne = (funct3==3'b001);
  assign f3bltu = (funct3==3'b110);
  assign f3bge = (funct3==3'b101);
  //End

    assign beq_taken  =  branch & f3beq & EX_MEM_Zflag;
  assign blt_taken  =  branch & f3blt & (EX_MEM_Nflag != EX_MEM_Vflag);
  assign bgeu_taken = branch & f3bgeu & EX_MEM_Cflag; // sltu -> ~C => sgeu -> C 
  assign bne_taken = branch & f3bne & ~EX_MEM_Zflag;
  assign bge_taken = branch & f3bge & (EX_MEM_Nflag==EX_MEM_Vflag);
  assign bltu_taken = branch & f3bltu & ~EX_MEM_Cflag;
  assign btaken = beq_taken | blt_taken | bgeu_taken | bne_taken | bge_taken | bltu_taken;
  
  
  assign branch_dest = (IF_ID_pc + se_br_imm);
  assign jal_dest    = (IF_ID_pc + se_jal_imm);
  assign jalr_dest = ( rs1_data+ se_imm_itype);

  
  
  //Start
  assign flush=(btaken | jal | jalr);
  //End
  wire [31:0] b2;
  assign b2 = alucontrol[4] ? ~rs2_data : rs2_data;
	
	adder_32bit iadder32 (.a   (rs1_data),
			     				.b   (b2),
								.cin (alucontrol[4]),
								.sum (sum),
								.N   (EX_MEM_Nflag),
								.Z   (EX_MEM_Zflag),
								.C   (EX_MEM_Cflag),
								.V   (EX_MEM_Vflag));	
	
	
	
  always @(posedge clk, posedge reset)
  begin
     if (reset)  pc <= #`simdelay 32'b0;
     else 
     begin
      //Start : If stall
      if(stall) pc<= pc;
            //End
      else if (btaken) // branch_taken
            pc <=  branch_dest;

         else if (jal) // jal
            pc <=  jal_dest;
         else if (jalr)
            pc <= jalr_dest;
         else 
            pc <= #`simdelay (pc + 4);
     end
  end




  //Start: 1. IF/ID F/F
  always @(posedge clk)
  begin
    if(stall)
      begin
      IF_ID_inst <= IF_ID_inst;
      IF_ID_pc <= IF_ID_pc;
      end
   //Start
   else if(flush)
   begin
   IF_ID_inst<=8'h13;
   IF_ID_pc<=32'b0;
   end
   //Emd
    else
       begin
        IF_ID_inst <= inst;
        IF_ID_pc <=  pc;
       end
  end
  //End

  //Start : 2. ID/EX F/F
  always @(posedge clk)
  begin
  //Start : stall 
    if(stall)
      begin
         ID_EX_alucontrol<= 5'b0;
      ID_EX_alusrc<= 1'b0;
         ID_EX_memwrite<= 1'b0;
   ID_EX_branch<= 1'b0;
   ID_EX_jal<= 1'b0;
   ID_EX_jalr<= 1'b0;
   ID_EX_auipc<= 1'b0;
   ID_EX_lui<= 1'b0;
   ID_EX_memread<= 1'b0;
   ID_EX_regwrite<= 1'b0;
   ID_EX_memtoreg<= 1'b0;
  ID_EX_rs1<= 5'b0;
  ID_EX_rs2<= 5'b0;
  ID_EX_rd<= 5'b0;
  ID_EX_rs1_data<= 32'b0;
  ID_EX_rs2_data<= 32'b0;
      end
   //End
  else
    begin
       ID_EX_alucontrol<= alucontrol;
      ID_EX_alusrc<= alusrc;
         ID_EX_memwrite<= memwrite;
      ID_EX_branch<= branch;
      ID_EX_jal<= jal;
      ID_EX_jalr<= jalr;
      ID_EX_auipc<= auipc;
      ID_EX_lui<= lui;
      ID_EX_memread<= memread;
      ID_EX_regwrite<= regwrite;
      ID_EX_memtoreg<= memtoreg;
     ID_EX_rs1<= rs1;
     ID_EX_rs2<= rs2;
     ID_EX_rd<= rd;
     ID_EX_rs1_data<= rs1_data;
     ID_EX_rs2_data<= rs2_data;
   ID_EX_se_jal_imm<= se_jal_imm;
     ID_EX_se_br_imm<= se_br_imm;
    ID_EX_se_imm_itype<= se_imm_itype;
     ID_EX_se_imm_stype<= se_imm_stype;
   ID_EX_auipc_lui_imm<= auipc_lui_imm;
  ID_EX_funct3 <=  funct3;
  ID_EX_pc<=IF_ID_pc;

    end
  end
  //End
  
  //Start: data hazard detection : memread=1 -> load case
always @(*)
 begin
  if(((ID_EX_rd==rs1) || (ID_EX_rd == rs2)) & ID_EX_memread) stall=1;
  else stall =0;
 end
//End
  
  //Start : 3. EX/MEM F/F
always @(posedge clk)
 begin
  EX_MEM_branch_dest <=  branch_dest;
  EX_MEM_jal_dest <=  jal_dest;
  EX_MEM_jalr_dest <= jalr_dest;
  EX_MEM_jalr_dest_tmp <=  jalr_dest_tmp;
  EX_MEM_rs2_data <=  ID_EX_rs2_data;
  EX_MEM_rd <=  ID_EX_rd;
  EX_MEM_aluout <=  aluout;
  
  EX_MEM_branch<= ID_EX_branch;
  EX_MEM_memwrite <=  ID_EX_memwrite;
  EX_MEM_memtoreg <=  ID_EX_memtoreg;
  EX_MEM_regwrite <=  ID_EX_regwrite;
  EX_MEM_jal <=  ID_EX_jal;
  EX_MEM_jalr <=  ID_EX_jalr;
  EX_MEM_memread <=  ID_EX_memread;
  EX_MEM_pc <=  ID_EX_pc;
 end

  //End

  //Start : 4.MEM/WB F/F
 always @(posedge clk)
  begin
 MEM_WB_rd <=  EX_MEM_rd;
 MEM_WB_aluout <=  EX_MEM_aluout;
 MEM_WB_MemRdata <=  MemRdata;
 
 MEM_WB_regwrite <=  EX_MEM_regwrite;
 MEM_WB_memtoreg <=  EX_MEM_memtoreg;
 MEM_WB_jal <=  EX_MEM_jal;
 MEM_WB_jalr <=  EX_MEM_jalr;
MEM_WB_pc <=  EX_MEM_pc;
  end

  //End

  
  // JAL immediate
  assign jal_imm[20:1] = {IF_ID_inst[31],IF_ID_inst[19:12],IF_ID_inst[20],IF_ID_inst[30:21]};
  assign se_jal_imm[31:0] = {{11{jal_imm[20]}},jal_imm[20:1],1'b0};
  
  // Branch immediate
  assign br_imm[12:1] = {IF_ID_inst[31],IF_ID_inst[7],IF_ID_inst[30:25],IF_ID_inst[11:8]};
  assign se_br_imm[31:0] = {{19{br_imm[12]}},br_imm[12:1],1'b0};

  
// Start : forward
always @(*)
 begin
  if((ID_EX_rd) && (rs1==ID_EX_rd) & ~ID_EX_memwrite)rs1_data=aluout;
  else if((EX_MEM_rd) && (rs1==EX_MEM_rd) & ~EX_MEM_memread)rs1_data=EX_MEM_aluout[31:0]; 
  else if((EX_MEM_rd) && (rs1==EX_MEM_rd) & EX_MEM_memread )rs1_data=MemRdata[31:0];
  else if((MEM_WB_rd) && (rs1==MEM_WB_rd))rs1_data=rd_data[31:0]; 
  else rs1_data = rf_rs1_data;
 end

always @(*)
begin
if((ID_EX_rd) && (rs2==ID_EX_rd) & ~ID_EX_memwrite)rs2_data=aluout;
  else if((EX_MEM_rd) && (rs2==EX_MEM_rd) & ~EX_MEM_memread )rs2_data=EX_MEM_aluout[31:0]; 
  else if((EX_MEM_rd) && (rs2==EX_MEM_rd) & EX_MEM_memread )rs2_data=MemRdata[31:0];
  else if((MEM_WB_rd) && (rs2==MEM_WB_rd))rs2_data=rd_data[31:0]; 
  else rs2_data=rf_rs2_data;
end 

//End


  // 
  // Register File 
  //
  regfile i_regfile(
    .clk         (clk),
    .we         (MEM_WB_regwrite),
    .rs1         (rs1),
    .rs2         (rs2),
    .rd         (MEM_WB_rd),
    .rd_data   (rd_data),
    .rs1_data   (rf_rs1_data),
    .rs2_data   (rf_rs2_data));


   assign MemWdata = EX_MEM_rs2_data;
   
   

     
   //
   // ALU 
   //
   alu i_alu(
      .a         (alusrc1),
      .b         (alusrc2),
      .alucont   (ID_EX_alucontrol),
      .result   (aluout),
      .N         (Nflag),
      .Z         (Zflag),
      .C         (Cflag),
      .V         (Vflag));

   // 1st source to ALU (alusrc1)
   always@(*)
   begin
        //Start : about forwarding
      if((EX_MEM_rd != 5'b0) && (EX_MEM_rd==ID_EX_rs1) && (EX_MEM_regwrite))alusrc1=EX_MEM_aluout[31:0];
           else if((MEM_WB_rd!=5'b0) && (MEM_WB_rd==ID_EX_rs1)&&(MEM_WB_regwrite))alusrc1=rd_data[31:0];
   //End
      else if      (ID_EX_auipc)   alusrc1[31:0]  =  ID_EX_pc;
      else if (ID_EX_lui)       alusrc1[31:0]  =  32'b0;
      else                alusrc1[31:0]  =  ID_EX_rs1_data[31:0];
   end
   
   // 2nd source to ALU (alusrc2)
   always@(*)
   begin
   //Start : about forwarding (no sign-extension)
      if((EX_MEM_rd!=5'b0) && (EX_MEM_rd==ID_EX_rs2) && (EX_MEM_regwrite==1) & (ID_EX_alusrc!=1))alusrc2=EX_MEM_aluout[31:0];
           else if((MEM_WB_rd!=5'b0) && (MEM_WB_rd==ID_EX_rs2) && (MEM_WB_regwrite==1)& (ID_EX_alusrc!=1))alusrc2=rd_data[31:0];
   //End
      else if     (ID_EX_auipc | ID_EX_lui)         alusrc2[31:0] = ID_EX_auipc_lui_imm[31:0];
      else if (ID_EX_alusrc & ID_EX_memwrite)   alusrc2[31:0] = ID_EX_se_imm_stype[31:0];
      else if (ID_EX_alusrc)               alusrc2[31:0] = ID_EX_se_imm_itype[31:0];
      else                           alusrc2[31:0] = ID_EX_rs2_data[31:0];
   end
   
   assign se_imm_itype[31:0] = {{20{IF_ID_inst[31]}},IF_ID_inst[31:20]};
   assign se_imm_stype[31:0] = {{20{IF_ID_inst[31]}},IF_ID_inst[31:25],IF_ID_inst[11:7]};
   assign auipc_lui_imm[31:0] = {IF_ID_inst[31:12],12'b0};


   // Data selection for writing to RF
   always@(*)
   begin
      if        (MEM_WB_jal | MEM_WB_jalr)         rd_data[31:0] = MEM_WB_pc + 4;
      else if (MEM_WB_memtoreg)   rd_data[31:0] = MEM_WB_MemRdata;
      else                  rd_data[31:0] = MEM_WB_aluout;
   end
   
endmodule