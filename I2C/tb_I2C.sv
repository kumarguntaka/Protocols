`include "uvm_macros.svh"
import uvm_pkg::*;

typedef enum {reset_dut, write_data, read_data} oper_mode;
///////////////////////////

class transaction extends uvm_sequence_item;
`umv_object_utils(transaction)

	function new(string path = "transaction");
		super.new("transaction");
	endfunction
	
	rand oper_mode op;
	rand logic [6:0] addr;
	rand logic [7:0] din;
		 bit rst;
		 bit wr;
		 logic [7:0] datard;
		 bit done;		 
endclass

///////////////////////////////////////

class reset_dut extends uvm_sequence #(transaction);
`umv_object_utils(reset_dut)
	
	function new(string path = "reset_dut");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body;
	repeat(5) begin
		start_item(tr);
		tr.op = reset_dut;
		assert(!tr.randomize());
		finish_item(tr);
	end
	endtask

endclass

///////////////////////////////////////////

class write_data extends uvm_sequence #(transaction);
`umv_object_utils(write_data)

	function new(string path = "write_data");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body;
	repeat(5) begin
		start_item(tr);
		tr.op = write_data;
		assert(!tr.randomize());
		finish_item(tr);
	end
	endtask

endclass

////////////////////////////////////////////

class read_data extends uvm_sequence #(transaction);
`umv_object_utils(read_data)
	
	function new(string path = "read_data");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body;
	repeat(5) begin
		start_item(tr);
		tr.op = read_data;
		assert(!tr.randomize());
		finish_item(tr);
	end
	endtask

endclass

//////////////////////////////////////////

class driver extends uvm_driver #(transaction);
`umv_component_utils(driver)

	function new (string path = "driver", uvm_component parent);
		super.new(path, parent);
	endfunction
	
	transaction tr;
	virtual i2c_i vif;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		tr = transaction::type_id::create("tr");
		
		if(!uvm_config_db #(virtual i2c_i)::get(this,"","vif",vif));
		`uvm_error("DRV","Unable to access the interface")
		
	endfunction
	
	virtual task run_phase(uvm_phase pahse);
		forever beign
			seq_item_port.get_next_item(tr);
			
			if(tr.op == reset_dut) begin
				`uvm_info("DRV", "System Reset", UVM_MEDIUM);
				vif.rst <= 1'b1;
				vif.wr <= 1'b0;
				vif.din <= 0;
				vif.addr <= 0;
				 @(posedge vif.clk);
			end
			
			else if(tr.op == write_data) begin
				vif.rst <= 1'b0;
				vif.wr <= 1'b1;
				vif.din <= tr.din;
				vif.addr <= tr.addr;
				`uvm_info("DRV", $sformatf("mode : write_data addr : %0d  din : %0d", tr.addr, tr.din), UVM_NONE);
				@(posedge vif.done);
			end
			
			else if(tr.op == read_data) begin
				vif.rst <= 1'b0;
				vif.wr <= 1'b0;
				vif.din <= tr.din;
				vif.addr <= tr.addr;
				`uvm_info("DRV", $sformatf("mode : READ addr : %0d  din : %0d", tr.addr, tr.din), UVM_NONE);
				@(posedge vif.done);  
			end
			
			seq_item_port.item_done(tr);
		end
	endtask
	
endclass

////////////////////////////////////////

class monitor extends uvm_monitor;
`uvm_component_utils(monitor)

	function new (string path = "monitor", uvm_component parent);
		super.new(path, parent);
	endfunction
	
	transaction tr;
	virtual i2c_i vif;
	uvm_analysis_port #(transaction) send;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		tr = transaction::type_id::create("tr");
		
		if(!uvm_config_db #(virtual i2c_i)::get(this,"","vif",vif));
		`uvm_error("MON","Unable to access the interface")
		
		send = new("send", this);
	endfunction
	
	virtual task run_phase(uvm_phase phase)
		forever begin
			if(vif.rst) begin
				@(posedge vif.clk);
				`uvm_info("MON", "System Reset", UVM_MEDIUM);
				tr.op = reset_dut;
				tr.rst = vif.rst;
				tr.wr = vif.wr;
				tr.din = vif.din;
				tr.addr = vif.addr;
				tr.datard = vif.datard;
				tr.done = vif.done;
				send.write(tr);
			end
			
			else if(vif.wr) begin
				@(posedge vif.done);
				tr.op = write_data;
				tr.rst = vif.rst;
				tr.wr = vif.wr;
				tr.din = vif.din;
				tr.addr = vif.addr;
				tr.datard = vif.datard;
				tr.done = vif.done;
				`uvm_info("DRV", $sformatf("mode : write_data addr : %0d  din : %0d", tr.addr, tr.din), UVM_NONE);
				send.write(tr);
			end
			
			else if(!vif.wr) begin
				@(posedge vif.done);
				tr.op = read_data;
				tr.rst = vif.rst;
				tr.wr = vif.wr;
				tr.din = vif.din;
				tr.addr = vif.addr;
				tr.datard = vif.datard;
				tr.done = vif.done;
				`uvm_info("DRV", $sformatf("mode : READ addr : %0d  din : %0d datard: %0d", tr.addr, tr.din, tr.datard), UVM_NONE);
				send.write(tr);
			end
		end
	endtask
endclass

////////////////////////////////////////////////////////////////////

class sco extends uvm_scoreboard;
`umv_component_utils(sco)

	function new (string path = "sco", uvm_component parent);
		super.new(path, parent);
	endfunction
	
	uvm_analysis_imp #(transaction) recv;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		recv = new("recv", this);
	endfunction
	
	virtual function void write(transaction tr);
		if(tr.op = reset_dut) begin
			`uvm_info("SCO","STSTEM RESET DETECTED", UVM_NONE)
		end
		
		else if(tr.op == write_data) begin
			arr[tr.addr] = tr.din;
			`uvm_info("SCO", $sformatf("DATA WRITE OP  addr:%0d, wdata:%0d arr_wr:%0d",tr.addr,tr.din,  arr[tr.addr]), UVM_NONE);
      end
 
		else if (tr.op == readd) begin
            data_rd = arr[tr.addr];
            if (data_rd == tr.datard)
                `uvm_info("SCO", $sformatf("DATA MATCHED : addr:%0d, rdata:%0d",tr.addr,tr.datard), UVM_NONE)
            else
                `uvm_info("SCO",$sformatf("TEST FAILED : addr:%0d, rdata:%0d data_rd_arr:%0d",tr.addr,tr.datard,data_rd), UVM_NONE) 
        end
		
		$dispaly("______________________________________");
		
	endfunction
endclass

//////////////////////////////////////////////////

class agent extends uvm_agent;
`uvm_component_utils(agent)

	function new (string path = "agent", uvm_component parent);
		super.new(path, parent);
	endfunction
	
	uvm_sequencer #(transaction) seqr;
	driver dr;
	monitor mon;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seqr = uvm_sequencer#(transaction)::type_id::create("seqr",this);
		dr = driver::type_id::create("dr",this);
		mon = monitor::type_id::create("mon",this);
	endfunction
	
	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		d.seq_item_port.connect(seqr.seq_item_export);
	endfunction
	
endclass

///////////////////////////////////////////////

class env extends uvm_environment;
`uvm_component_utils(env)

	function new (string path = "agent", uvm_component parent);
		super.new(path, parent);
	endfunction
	
	agent a;
	sco s;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		a = agent::type_id::create("a",this);
		s = sco::type_id::create("sco",this);
	endfunction
	
	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		a.m.send.connect(s.recv);
	endfunction
	
endclass
///////////////////////////////////////////

class test extends uvm_test;
`uvm_component_utils(test)

	function new (string path = "test", uvm_component parent);
		super.new(path, parent);
	endfunction
	
	env e;
	write_data wdata;
	read_data rdata;
	reset_dut rst_dut;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		e = env::type_id::create("e",this);
		wdata = write_data::type_id::create("wdata",this);
		rdata = read_data::type_id::create("rdata",this);
		rst_dut = reset_dut::type_id::create("rst_dut",this);
	endfunction
	
	virtual task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		
		rst_dut.start(e.a.seqr);
		write_data.start(e.a.seqr);
		read_data.start(e.a.seqr);
		
		phase.drop_opjection(this);
	endtask
	
endclass

////////////////////////////////////////////

module tb;
  
  i2c_i vif();
  
  i2c_mem dut  (.clk(vif.clk), 
				.rst(vif.rst), 
				.wr(vif.wr), 
				.addr(vif.addr), 
				.din(vif.din), 
				.datard(vif.datard), 
				.done(vif.done));
  
	initial begin
		vif.clk <= 0;
	end
 
	always #10 vif.clk <= ~vif.clk;
 
	initial begin
		uvm_config_db#(virtual i2c_i)::set(null, "*", "vif", vif);
		run_test("test");
	end
   
	initial begin
		$dumpfile("dump.vcd");
		$dumpvars;
	end

endmodule