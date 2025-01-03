class test extends uvm_test;

`uvm_component_utils(test)
 
	function new(input string inst = "test", uvm_component c);
		super.new(inst,c);
	endfunction
 
	env e;
	write_data wdata;
	write_err werr;
  
	read_data rdata;
	read_err rerr;
  
	write_read wrrdb;
 
	reset_dut rstdut;  
 
  
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		e      = env::type_id::create("env",this);
		wdata  = write_data::type_id::create("wdata");
		werr   = write_err::type_id::create("werr");
		rdata  = read_data::type_id::create("rdata");
		wrrdb  = writeb_readb::type_id::create("wrrdb");
		rerr   = read_err::type_id::create("rerr");
		rstdut = reset_dut::type_id::create("rstdut");
	endfunction
 
	virtual task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		wrrdb.start(e.a.seqr);
		#20;
		phase.drop_objection(this);
	endtask

endclass