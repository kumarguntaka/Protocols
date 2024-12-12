class driver extends uvm_driver #(transaction);

`uvm_component_utils(driver)

	function new(string path = "driver", uvm_component parent);
		super.new(path, parent);
	endfunction
	
	transaction tr;
	virtual spi_i vif;
	
	virtual function void build_phase(uvm_phase phase);
		super.build_phase(phase);
		
		tr = transaction::type_id::create("tr");
		
		if(!config_db #(virtual spi_i)::get(this,"","vif",vif));
			`uvm("drv","unable to access interface")
			
	endfunction
	
	task reset_dut();
		repeat(5) begin
			vif.rst      <= 1'b1;
			vif.addr     <= 'h0;
			vif.din      <= 'h0;
			vif.wr       <= 1'b0; 
			`uvm_info("DRV", "System Reset : Start of Simulation", UVM_MEDIUM)
			@(posedge vif.clk);
		end
	endtask
	
	task drive();
		forever begin
			seq_item_port.get_next_item(tr);
			
			if(tr.op = reset_dut) begin
				vif.rst <= 1'b1;
				@(posedge vif.clk)
			end
			
			else if(tr.op = write_data) begin
				vif.rst <= 1'b0;
				vif.wr <= 1'b1;
				vif.addr <= tr.addr;
				vif.din <= tr.din;
				@(posedge vif.clk);
				`uvm_info("DRV_write_data",$sformat("mode : Write, rst: %b, wr: %b, addr:%0d, din:%0d", vif.rst, vif.wr, vif.addr, vif.din"),UVM_MEDIUM)
				@(posedge vif.done);
				end
			
			else if(tr.op = read_data) begin
				vif.rst <= 1'b0;
				vif.wr <= 1'b0;
				vif.addr <= tr.addr;
				vif.din <= tr.din;
				@(posedge vif.clk);
				`uvm_info("DRV_read_data",$sformat("mode : read, rst: %b, wr: %b, addr:%0d, din:%0d", vif.rst, vif.wr, vif.addr, vif.din"),UVM_MEDIUM)
				@(posedge vif.done);
				end
			
			seq_item_port.item_done();
		end
	endtask
	
	virtual task run_phase(uvm_phase phase);
		drive();
	endtask

endclass