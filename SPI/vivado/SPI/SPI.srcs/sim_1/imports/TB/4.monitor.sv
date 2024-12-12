class monitor extends uvm_monitor;

`uvm_component_utils(monitor)

    function new(input string path = "monitor", uvm_component parent);
		super.new(path,parent);
    endfunction
	
	transaction tr;
	virtual spi_i vif;
	uvm_analysis_port #(transaction) send;
	
	virtual function void build_phase(uvm_phase pahse);
		super.build_phase(phase);
		tr = transaction::type_id::create("tr");
		send = new("send", this);
		if(!uvm_config_db#(virtual spi_i)::get(this,"","vif",vif))
        `uvm_error("MON","Unable to access Interface");
    endfunction
	
	virtual task run_phase(uvm_phase phase);
		forever begin
			@(posedge vif.clk);
			if(vif.rst) begin
				tr.op = reset_dut;
				`uvm_info("MON", "SYSTEM RESET DETECTED", UVM_NONE);
				send.write(tr);
			end
			
			else if (!vif.rst && vif.wr) begin
			@(posedge vif.done);
				tr.op     = write_data;
				tr.din    = vif.din;
				tr.addr   = vif.addr;
				tr.err    = vif.err;
				`uvm_info("MON", $sformatf("DATA WRITE addr:%0d data:%0d err:%0d",tr.addr,tr.din,tr.err), UVM_NONE); 
				send.write(tr);
			end
			
			else if (!vif.rst && !vif.wr) begin
			@(posedge vif.done);
				tr.op     = read_data;
				tr.dout    = vif.dout;
				tr.addr   = vif.addr;
				tr.err    = vif.err;
				`uvm_info("MON", $sformatf("DATA WRITE addr:%0d data:%0d err:%0d",tr.addr,tr.din,tr.err), UVM_NONE); 
				send.write(tr);
			end
			
		end
	endtask
	
endclass