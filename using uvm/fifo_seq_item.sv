package fifo_seq_item_pkg;
import uvm_pkg::*;
`include "uvm_macros.svh"

  parameter FIFO_WIDTH = 16;
  parameter FIFO_DEPTH = 8;

class fifo_seq_item extends uvm_sequence_item;
  `uvm_object_utils(fifo_seq_item);

  rand logic rst_n, wr_en, rd_en; 
  rand logic [FIFO_WIDTH-1:0] data_in; 
  logic [FIFO_WIDTH-1:0] data_out;
  logic wr_ack, overflow;
  logic full, empty, almostfull, almostempty, underflow;

  int RD_EN_ON_DIST = 30;
  int WR_EN_ON_DIST = 70;   

  function new (string name = "fifo_seq_item");
    super.new (name);
  endfunction  

  function string convert2string();
      return $sformatf("%s rst_n=%b data_in=%b data_out=%b ",super.convert2string(),rst_n,data_in,data_out);
  endfunction    

  function string convert2string_stimulus();
      return $sformatf(" rst_n=%b data_in=%b data_out=%b",rst_n,data_in,data_out);
  endfunction  

  constraint rst_n_c { 
    rst_n dist {0:=1 , 1:=99};
    }

  constraint wr_en_c { 
    wr_en dist {0:=(100-WR_EN_ON_DIST) , 1:=WR_EN_ON_DIST};
    }

  constraint rd_en_c { 
    rd_en dist {0:=(100-RD_EN_ON_DIST) , 1:=RD_EN_ON_DIST};
    }
   

endclass

endpackage