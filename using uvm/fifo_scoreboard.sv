package fifo_sco_pkg;
import fifo_seq_item_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"  
  
  class fifo_sco extends uvm_scoreboard;
    `uvm_component_utils(fifo_sco)

    uvm_analysis_export #(fifo_seq_item) sb_export;
    uvm_tlm_analysis_fifo # (fifo_seq_item) sb_fifo;
    fifo_seq_item seq_item_sb;

    parameter FIFO_WIDTH = 16;
    parameter FIFO_DEPTH = 8;
    localparam max_fifo_addr = $clog2(FIFO_DEPTH);
    logic [FIFO_WIDTH-1:0] data_out_ref;
    logic [FIFO_WIDTH-1:0] Queue [$] ;    
    logic [max_fifo_addr:0] count;

    int error_count = 0;
    int correct_count = 0;
    
  function new (string name = "fifo_sco" , uvm_component parent = null);
    super.new (name,parent);
  endfunction 

    function void build_phase (uvm_phase phase);
    super.build_phase (phase);
    sb_export = new("sb_export",this);
    sb_fifo = new("sb_fifo",this);
  endfunction

  function void connect_phase(uvm_phase phase);
   super.connect_phase(phase);
   sb_export.connect(sb_fifo.analysis_export);
  endfunction  

  task run_phase (uvm_phase phase);
   super.run_phase(phase);
   forever begin
    sb_fifo.get(seq_item_sb);
    #1;
    ref_model(seq_item_sb);
    if ((seq_item_sb.data_out != data_out_ref)) begin
        `uvm_error("run_phase",$sformatf("compartion failled while ref = %b",data_out_ref))
        error_count++;
    end
    else 
       correct_count++;
   end
  endtask

  task ref_model (fifo_seq_item seq_item_chk);

			if (!seq_item_chk.rst_n) begin
				Queue <= {}; 
				count <= 0;
			end
			else begin

				if (seq_item_chk.wr_en && count <  FIFO_DEPTH) begin
					Queue.push_back(seq_item_chk.data_in);  
					count <= Queue.size();       
				end

				if (seq_item_chk.rd_en && count != 0) begin
					data_out_ref <= Queue.pop_front();
					count <= Queue.size();          
				end
			end
  endtask

  function void report_phase (uvm_phase phase);
   super.report_phase(phase);
   `uvm_info("report_phase",$sformatf("corect = %d",correct_count) , UVM_MEDIUM)
   `uvm_info("report_phase",$sformatf("error = %d",error_count) , UVM_MEDIUM)
  endfunction
  endclass 
  endpackage