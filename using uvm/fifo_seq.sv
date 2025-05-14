package fifo_seq_pkg;
import uvm_pkg::*;
import fifo_seq_item_pkg::*;
`include "uvm_macros.svh"

class fifo_reset_seq extends uvm_sequence #(fifo_seq_item);
  `uvm_object_utils(fifo_reset_seq)
   fifo_seq_item seq_item;

    function new(string name = "fifo_reset_seq");
        super.new(name);
    endfunction 

    task body;
       seq_item = fifo_seq_item::type_id::create("seq_item");
       start_item(seq_item);
       //#0; seq_item.rst_n = 1; #0;
       seq_item.rst_n = 0;
       $assertoff;
       finish_item (seq_item);
    endtask
endclass 

class fifo_main1_seq extends uvm_sequence #(fifo_seq_item);
  `uvm_object_utils(fifo_main1_seq)
   fifo_seq_item seq_item;

    function new(string name = "fifo_main1_seq");
        super.new(name);
    endfunction 

    task body;
       seq_item = fifo_seq_item::type_id::create("seq_item");
       $asserton;
       seq_item.wr_en = 1;
       seq_item.rd_en = 0;
       seq_item.wr_en.rand_mode(0);
       seq_item.rd_en.rand_mode(0);
       repeat (999) begin 
       start_item(seq_item);
       assert (seq_item.randomize());
       finish_item (seq_item);
       end
    endtask
endclass 

class fifo_main2_seq extends uvm_sequence #(fifo_seq_item);
  `uvm_object_utils(fifo_main2_seq)
   fifo_seq_item seq_item;

    function new(string name = "fifo_main2_seq");
        super.new(name);
    endfunction 

    task body;
       seq_item = fifo_seq_item::type_id::create("seq_item");
       seq_item.wr_en = 0;
       seq_item.rd_en = 1;
       seq_item.wr_en.rand_mode(0);
       seq_item.rd_en.rand_mode(0);
       repeat (999) begin 
       start_item(seq_item);
       assert (seq_item.randomize());
       finish_item (seq_item);
       end
    endtask
endclass

class fifo_main3_seq extends uvm_sequence #(fifo_seq_item);
  `uvm_object_utils(fifo_main3_seq)
   fifo_seq_item seq_item;

    function new(string name = "fifo_main3_seq");
        super.new(name);
    endfunction 

    task body;
       seq_item = fifo_seq_item::type_id::create("seq_item");
       repeat (99999) begin 
       start_item(seq_item);
       assert (seq_item.randomize());
       finish_item (seq_item);
       end
    endtask
endclass
endpackage