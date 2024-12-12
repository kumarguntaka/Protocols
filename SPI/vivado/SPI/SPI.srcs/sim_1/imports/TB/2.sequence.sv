class reset_dut extends uvm_sequence #(transaction);

`uvm_object_utils(reset_dut)

	function new(string path = "reset_dut");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body();
	tr = transaction::type_id::create("tr");
	repeat(10) begin
		tr.addr_c.constraint_mode(1);
        tr.addr_err.constraint_mode(0);
		start_item(tr);
		assert(tr.randomize());
		tr.op = reset_dut;
		finish_item(tr);
		end
	endtask
	
endclass

/////////////////////////////////////////////

class write_data extends uvm_sequence #(transaction);

`uvm_object_utils(write_data)

	function new(string path = "write_data");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body();
	tr = transaction::type_id::create("tr");
	repeat(10) begin
		tr.addr_c.constraint_mode(1);
        tr.addr_err.constraint_mode(0);
		start_item(tr);
		assert(tr.randomize());
		tr.op = write_data;
		finish_item(tr);
		end
	endtask
	
endclass

/////////////////////////////////////////////

class read_data extends uvm_sequence #(transaction);

`uvm_object_utils(read_data)

	function new(string path = "read_data");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body();
	tr = transaction::type_id::create("tr");
	repeat(10) begin
		tr.addr_c.constraint_mode(1);
        tr.addr_err.constraint_mode(0);
		start_item(tr);
		assert(tr.randomize());
		tr.op = read_data;
		finish_item(tr);
		end
	endtask
	
endclass

/////////////////////////////////////////////

class write_err extends uvm_sequence #(transaction);

`uvm_object_utils(write_err)

	function new(string path = "write_err");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body();
	tr = transaction::type_id::create("tr");
	repeat(10) begin
		tr.addr_c.constraint_mode(0);
        tr.addr_err.constraint_mode(1);
		start_item(tr);
		assert(tr.randomize());
		tr.op = write_data;
		finish_item(tr);
		end
	endtask
	
endclass

/////////////////////////////////////////
class read_err extends uvm_sequence #(transaction);

`uvm_object_utils(read_err)

	function new(string path = "read_err");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body();
	tr = transaction::type_id::create("tr");
	repeat(10) begin
		tr.addr_c.constraint_mode(0);
        tr.addr_err.constraint_mode(1);
		start_item(tr);
		assert(tr.randomize());
		tr.op = read_data;
		finish_item(tr);
		end
	endtask
	
endclass

/////////////////////////////////////////
class write_read extends uvm_sequence #(transaction);

`uvm_object_utils(write_read)

	function new(string path = "write_read");
		super.new(path);
	endfunction
	
	transaction tr;
	
	virtual task body();
	tr = transaction::type_id::create("tr");
	repeat(10) begin
		tr.addr_c.constraint_mode(0);
        tr.addr_err.constraint_mode(1);
		start_item(tr);
		assert(tr.randomize());
		tr.op = write_data;
		finish_item(tr);
		end
	
	repeat(10) begin
		tr.addr_c.constraint_mode(0);
        tr.addr_err.constraint_mode(1);
		start_item(tr);
		assert(tr.randomize());
		tr.op = read_data;
		finish_item(tr);
		end
	endtask
	
endclass