
typedef enum {reset_dut, write, read, write_err, read_err, write_read} oper_mode;

class transaction extends uvm_sequence_item;

`uvm_object_utils(transaction)
		
	rand oper_mode op;	
		 bit rst;
		 bit wr;
	rand logic [7:0] din;
	rand logic [7:0] addr;
		 bit done;
		 bit err;
		 logic [7:0] dout;

	constraint addr_c {addr < 10;};
	constraint addr_err {addr > 32;};
	
	/*    `uvm_object_utils_begin(transaction)
        `uvm_field_int (wr,UVM_ALL_ON)
        `uvm_field_int (rst,UVM_ALL_ON)
        `uvm_field_int (addr,UVM_ALL_ON)
        `uvm_field_int (din,UVM_ALL_ON)
        `uvm_field_int (dout,UVM_ALL_ON)
        `uvm_field_int (done,UVM_ALL_ON)
        `uvm_field_int (err,UVM_ALL_ON)
        `uvm_field_enum(oper_mode, op, UVM_DEFAULT)
        `uvm_object_utils_end
		*/
	function new(string path = "transaction");
		super.new(path);
	endfunction

endclass

//////////////////////////

class spi_config extends uvm_object;

`uvm_object_utils(spi_config)

	uvm_active_passive_enum is_active = UVM_ACTIVE;	
	
	function new(string path = "spi_config");
		super.new(path);
	endfunction

endclass 