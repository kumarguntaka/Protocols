`import"uvm.macros.svh"
import uvm_pkg::*;

class apb_config extends uvm_object;
`uvm_object_utils(apb_config)

	function new(string name = "apb_config");
		super.new(name);
	endfunction
	
	uvm_active_passive_enum is_active = UVM_ACTIVE;
	
endclass
/////////////////////////////////////////////

typedef enum bit[1:0] {reset_dut=0, write_data=1, read_data=2} oper_mode;

///////////////////////////////
class transaction extends uvm_sequence_item;
`uvm_object_utils(transaction)

	function new(string name = "transaction");
		super.new(name);
	endfunction
	
	rand oper_mode op;
	rand logic [31:0] paddr;
	rand logic [31:0] pwdata;
		 logic presetn;
		 logic psel;
		 logic penable;
		 logic pwrite;
		 logic [31:0] prdata;
		 logic pready;
		 logic pslverr;
		 
	constraint addr_c {paddr <= 31;}
	constraint addr_c_err {paddr > 31;}
endclass

/////////////////////////////////////////
class reset_dut extends uvm_sequence #(transaction);
`uvm_object_utils(reset_dut)

	function new(string name = "reset_dut");
		super.new(name);
	endfunction
	
	transaction tr;
	
	virtual task body();
		repeat(20) begin;
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(1);
		tr.addr_c_err.constraint_mode(0);
		
		start_item(tr);
		tr.op = reset_dut;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
	endtask
endclass

//////////////////////////////////////
class write_data extends uvm_sequence #(transaction);
`uvm_object_utils(write_data)

	function new(string name = "write_data");
		super.new(name);
	endfunction
	
	transaction tr;
	
	virtual task body();
		repeat(20) begin;
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(1);
		tr.addr_c_err.constraint_mode(0);
		
		start_item(tr);
		tr.op = write_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
	endtask
endclass

//////////////////////////////////////
class read_data extends uvm_sequence #(transaction);
`uvm_object_utils(read_data)

	function new(string name = "read_data");
		super.new(name);
	endfunction
	
	transaction tr;
	
	virtual task body();
		repeat(20) begin;
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(1);
		tr.addr_c_err.constraint_mode(0);
		
		start_item(tr);
		tr.op = read_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
	endtask
endclass

////////////////////////////////////////////
class write_read_data extends uvm_sequence #(transaction);
`uvm_object_utils(write_read_data)

	function new(string name = "write_read_data");
		super.new(name);
	endfunction
	
	transaction tr;
	
	virtual task body();
		repeat(20) begin;
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(1);
		tr.addr_c_err.constraint_mode(0);
		
		start_item(tr);
		tr.op = write_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		
		start_item(tr);
		tr.op = read_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
	endtask
endclass

///////////////////////////////////////
class write_after_read_data extends uvm_sequence #(transaction);
`uvm_object_utils(write_after_read_data)

	function new(string name = "write_after_read_data");
		super.new(name);
	endfunction
	
	transaction tr;
	
	virtual task body();
		repeat(20) begin;
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(1);
		tr.addr_c_err.constraint_mode(0);
		
		start_item(tr);
		tr.op = write_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
		
		repeat(20) begin
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(1);
		tr.addr_c_err.constraint_mode(0);
		
		start_item(tr);
		tr.op = read_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
	endtask
endclass

////////////////////////////////////
class write_err extends uvm_sequence #(transaction);
`uvm_object_utils(write_err)

	function new(string name = "write_err");
		super.new(name);
	endfunction
	
	transaction tr;
	
	virtual task body();
		repeat(20) begin;
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(0);
		tr.addr_c_err.constraint_mode(1);
		
		start_item(tr);
		tr.op = write_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
	endtask
endclass

///////////////////////////
class read_err extends uvm_sequence #(transaction);
`uvm_object_utils(read_err)

	function new(string name = "read_err");
		super.new(name);
	endfunction
	
	transaction tr;
	
	virtual task body();
		repeat(20) begin;
		tr = transaction::type_id::create("tr");
		tr.addr_c.constraint_mode(0);
		tr.addr_c_err.constraint_mode(1);
		
		start_item(tr);
		tr.op = read_data;
		assert(tr.randomize(tr));
		finish_item(tr);
		end
	endtask
endclass

//////////////////////////////////
class driver extends uvm_driver #(transaction);
`uvm_component_utils(driver)

	function new(string name = "driver", uvm_component parent);
		super.new(name,parent);
	endfunction
	
	transaction tr;
	virtual apb_if vif;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		tr = transaction::type_id::create("tr");
		
		if(!uvm_config_db::(virtual apb_if)::get(this,"","vif",vif));
		`uvm_error("DRV","Unable to access the Interface");
	endfunction
	
	virtual task run_phase(uvm_phase phase);
		drive();
	endtask
	
	task reset();
		repeat(10) begin
		vif.presetn <= 1'b0;
		vif.paddr   <= 'h0;
		vif.pwdata  <= 'h0;
		vif.pwrite  <= 'b0;
		vif.psel    <= 'b0;
		vif.penable <= 'b0;
		`uvm_info("DRV","SYSTEM RESET: Start of simulation", UVM_MEDIUM)
		@(posedge vif.pclk);
		end
	endtask

	task drive();
		reset();
		forever begin
			seq_item_port.get_next_item(tr);
			
			if(tr.op == rst) begin
                vif.presetn   <= 1'b0;
                vif.paddr     <= 'h0;
                vif.pwdata    <= 'h0;
                vif.pwrite    <= 'b0;
                vif.psel      <= 'b0;
                vif.penable   <= 'b0;
                @(posedge vif.pclk);  
            end
			
			else if(tr.op == write_data) begin
				vif.presetn   <= 1'b1;
                vif.paddr     <= tr.paddr;
                vif.pwdata    <= tr.pwdata;
                vif.pwrite    <= 'b1;
                vif.psel      <= 'b1;
                @(posedge vif.pclk); 
			    vif.penable   <= 'b1;
				`uvm_info("DRV", $sformatf("mode:%0s, addr:%0d, wdata:%0d, rdata:%0d, slverr:%0d",tr.op.name(),tr.paddr,tr.pwdata,tr.prdata,tr.pslverr), UVM_NONE);
				@(negedge vif.pready);
				vif.penable   <= 1'b0;
				tr.pslverr = vif.pslverr;
			end
			
			else if(tr.op == read_data) begin
				vif.presetn   <= 1'b1;
                vif.paddr     <= tr.paddr;
                vif.pwrite    <= 'b0;
                vif.psel      <= 'b1;
                @(posedge vif.pclk); 
			    vif.penable   <= 'b1;
				`uvm_info("DRV", $sformatf("mode:%0s, addr:%0d, wdata:%0d, rdata:%0d, slverr:%0d",tr.op.name(),tr.paddr,tr.pwdata,tr.prdata,tr.pslverr), UVM_NONE);
				@(negedge vif.pready);
				vif.penable	  <= 1'b0;
				tr.pslverr = vif.pslverr;
				tr.prdata = vif.prdata;
			end
				
			seq_item_port.item_done(tr);
		end
	
endclass

/////////////////////////////////////
class monitor extends uvm_monitor;
`uvm_component_utils(monitor)

    function new(input string path = "monitor", uvm_component parent = null);
		super.new(path,parent);
    endfunction
	
	transaction tr;
	virtual apb_if vif;
	uvm_analysis_port #(transaction) send;
	
	virtual function void build_phase(uvm_phase phase);
		tr = transaction::type_id::create("tr");
		send = new("send", this);
		if(!uvm_config_db#(virtual apb_if)::get(this,"","vif",vif))
        `uvm_error("MON","Unable to access Interface");
	endfunction
	
	virtual task run_phase(uvm_phase phase);
    forever begin
      @(posedge vif.pclk);
		if(!vif.presetn) begin
			tr.op      = rst; 
			`uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
			send.write(tr);
        end
		
		else if (vif.presetn && vif.pwrite)	begin
			@(negedge vif.pready);
			tr.op     = write_data;
			tr.pwdata = vif.pwdata;
			tr.paddr  =  vif.paddr;
			tr.pslverr  = vif.pslverr;
			`uvm_info("MON", $sformatf("DATA WRITE addr:%0d data:%0d slverr:%0d",tr.PADDR,tr.PWDATA,tr.PSLVERR), UVM_NONE); 
			send.write(tr);
        end
      
		else if (vif.presetn && !vif.pwrite) begin
			@(negedge vif.pready);
			tr.op     = read_data; 
			tr.paddr  =  vif.paddr;
			tr.prdata   = vif.prdata;
			tr.pslverr  = vif.pslverr;
			`uvm_info("MON", $sformatf("DATA READ addr:%0d data:%0d slverr:%0d",tr.PADDR, tr.PRDATA,tr.PSLVERR), UVM_NONE); 
			send.write(tr);
        end
    end
	endtask 
endclass

////////////////////////////////////////
class sco extends uvm_scoreboard;
`uvm_component_utils(sco)

    function new(input string path = "sco", uvm_component parent = null);
		super.new(path,parent);
    endfunction
	
	uvm_analysis_imp#(transaction,sco) recv;
	bit [31:0] arr[32] = '{default:0};
	bit [31:0] addr    = 0;
	bit [31:0] data_rd = 0;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		recv = new("recv", this);
    endfunction
	
	virtual function void write(transaction tr);
		if(tr.op == reset_dut) begin
            `uvm_info("SCO", "SYSTEM RESET DETECTED", UVM_NONE);
        end  
    
		else if (tr.op == write_data) begin
            if(tr.pslverr == 1'b1) begin
                `uvm_info("SCO", "SLV ERROR during WRITE OP", UVM_NONE);
            end
            else begin
				arr[tr.paddr] = tr.pwdata;
				`uvm_info("SCO", $sformatf("DATA WRITE OP  addr:%0d, wdata:%0d arr_wr:%0d",tr.PADDR,tr.PWDATA,  arr[tr.PADDR]), UVM_NONE);
            end
		end
    
		else if (tr.op == read_data) begin
			if(tr.pslverr == 1'b1) begin
                `uvm_info("SCO", "SLV ERROR during READ OP", UVM_NONE);
            end
            else begin
                data_rd = arr[tr.paddr];
                if (data_rd == tr.prdata)
                 	`uvm_info("SCO", $sformatf("DATA MATCHED : addr:%0d, rdata:%0d",tr.PADDR,tr.PRDATA), UVM_NONE)
                else
                    `uvm_info("SCO",$sformatf("TEST FAILED : addr:%0d, rdata:%0d data_rd_arr:%0d",tr.PADDR,tr.PRDATA,data_rd), UVM_NONE) 
                end
		end
     
    $display("----------------------------------------------------------------");
    endfunction

endclass
/////////////////////////////////////

class agent extends uvm_agent;
`uvm_component_utils(agent)

	function new(input string path = "agent", uvm_component parent = null);
		super.new(path,parent);
    endfunction
	
	uvm_sequencer #(transaction) seqr;
	driver dvr;
	monitor mon;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		seqr = uvm_sequencer #(transaction)::type_id::create("seqr");
		drv = driver::type_id::create("drv",this);
		mon = monitor::type_id::create("mon",this);
    endfunction
	
	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		if(cfg.is_active == UVM_ACTIVE) begin
		drv.seq_item_port.connect(seqr.seq_item_export);
		end
	endfunction
endclass

/////////////////////////////////////////

class env extends uvm_environment;
`uvm_component_utils(env)

	function new(input string path = "env", uvm_component parent = null);
		super.new(path,parent);
    endfunction
	
	agent a;
	sco s;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		a = agent::type_id::create("a",this);
		s = sco::type_id::create("s",this);
    endfunction
	
	virtual function void connect_phase(uvm_phase phase);
		super.connect_phase(phase);
		a.mon.send.connect(s.recv);
	endfunction
endclass

///////////////////////////////
class test extends uvm_test;
`uvm_component_utils(test)

	function new(input string path = "test", uvm_component parent = null);
		super.new(path,parent);
    endfunction
	
	env e;
	reset_dut rst;
	write_data wdata;
	read_data rdata;
	write_read_data w_r_data;
	write_err werr;
	read_err rerr;
	write_after_read_data w_af_r_data;

	virtual function void build_phase(uvm_phase phase);\
		super.build_phase(phase);
		e = env::type_id::create("e", this);
		rst = reset_dut::type_id::create("rst");
		wdata = write_data::type_id::create("wdata");
		rdata = read_data::type_id::create("rdata");
		werr = write_err::type_id::create("werr");
		rerr = read_err::type_id::create("rerr");
		w_r_data = write_read_data::type_id::create("w_r_data");
		w_af_r_data = write_after_read_data::type_id::create("w_af_r_data");
	endfunction

	virtual task run_phase(uvm_phase phase);
		phase.raise_objection(this);
		wdata.start(e.a.seqr);
		#20;
		phase.drop_objection(this);
	endtask
endclass

//////////////////////////////////////////////
module tb;

	apb_if vif();
	
	apb_ram dut(.presetn(vif.presetn), 
				.pclk(vif.pclk), 
				.psel(vif.psel), 
				.penable(vif.penable), 
				.pwrite(vif.pwrite), 
				.paddr(vif.paddr), 
				.pwdata(vif.pwdata), 
				.prdata(vif.prdata), 
				.pready(vif.pready), 
				.pslverr(vif.pslverr));
				
	initial begin
		vif.pclk <= 0;
	end
	
	always #10 vif.pck <= ~vif.pclk;
	
	initial begin
		uvm_config_db#(virtual apb_if)::set(null, "*", "vif", vif);
		run_test("test");
	end
  
	initial begin
		$dumpfile("dump.vcd");
		$dumpvars;
	end 
endmodule