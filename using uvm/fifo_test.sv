
package fifo_test_pkg;
import fifo_env_pkg::*;
import fifo_conf_pkg::*;
import fifo_seq_pkg::*;
import uvm_pkg::*;
`include "uvm_macros.svh"

class fifo_test extends uvm_test;

  `uvm_component_utils (fifo_test) 

  fifo_env env;
  fifo_config fifo_cfg;
  virtual fifo_if fifo_vif;
  fifo_main1_seq main1_seq;
  fifo_main2_seq main2_seq;
  fifo_main3_seq main3_seq;
  fifo_reset_seq reset_seq;

  function new (string name = "fifo_env" , uvm_component parent = null);
    super.new (name,parent);
  endfunction   

  function void build_phase (uvm_phase phase);
    super.build_phase(phase);
    env = fifo_env::type_id::create ("env",this);
    fifo_cfg = fifo_config::type_id::create ("fifo_cfg");
    main1_seq = fifo_main1_seq::type_id::create("main1_seq");
    main2_seq = fifo_main2_seq::type_id::create("main2_seq");
    main3_seq = fifo_main3_seq::type_id::create("main3_seq");
    reset_seq = fifo_reset_seq::type_id::create("reset_seq");

    if (!uvm_config_db#(virtual fifo_if)::get(this,"","fifo_IF",fifo_cfg.fifo_vif))
       `uvm_fatal ("build_phase","test - unable to get the virtual interface");

       uvm_config_db#(fifo_config)::set(this,"*","CFG",fifo_cfg); 

  endfunction

  task run_phase (uvm_phase phase);
    super.run_phase(phase);
    phase.raise_objection(this);

    //reset
    `uvm_info ("run_phase" , "reset asserted" , UVM_LOW)
    reset_seq.start(env.agt.sqr);
    `uvm_info ("run_phase" , "reset deasserted" , UVM_LOW)
    
    
    //main1
    `uvm_info ("run_phase" , "stimulus generation started 1" , UVM_LOW)
    main1_seq.start(env.agt.sqr);
    `uvm_info ("run_phase" , "stimulus generation ended 1" , UVM_LOW)   
    
    //main2
    `uvm_info ("run_phase" , "stimulus generation started 2" , UVM_LOW)
    main2_seq.start(env.agt.sqr);
    `uvm_info ("run_phase" , "stimulus generation ended 2" , UVM_LOW)  

    //main3
    `uvm_info ("run_phase" , "stimulus generation started 3" , UVM_LOW)
    main3_seq.start(env.agt.sqr);
    `uvm_info ("run_phase" , "stimulus generation ended 3" , UVM_LOW)          
    
    //reset
    `uvm_info ("run_phase" , "reset asserted" , UVM_LOW)
    reset_seq.start(env.agt.sqr);
    `uvm_info ("run_phase" , "reset deasserted" , UVM_LOW)     

    phase.drop_objection(this);
  endtask

endclass: fifo_test
endpackage