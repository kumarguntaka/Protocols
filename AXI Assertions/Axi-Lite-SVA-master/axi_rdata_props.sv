interface axic_rdata
	#(
		parameter integer maxwait = 5,
		parameter integer C_AXI_DATA_WIDTH = 32,
		parameter integer C_AXI_ADDR_WIDTH = 8
	)
	(
		input wire AXI_ACLK,
		input wire AXI_ARESETN,
		input wire[C_AXI_DATA_WIDTH-1:0] AXI_RDATA,
		input wire AXI_RVALID,
		input wire AXI_RREADY
	);

	property AXI4_ERRS_RDATA_STABLE; //RDATA remains stable when RVALID is asserted, and RREADY is LOW.
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_RVALID & !AXI_RREADY & !$isunknown({AXI_RVALID, AXI_RREADY})
			##1 AXI_ARESETN
			|-> $stable(AXI_RDATA);
	endproperty
	AXI4_ERRS_RDATA_STABLE_inst: assert property (AXI4_ERRS_RDATA_STABLE);

	property AXI4_ERRS_RDATA_X; //A value of X on RDATA valid byte lanes is not permitted when RVALID is HIGH
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_RVALID
			|-> !$isunknown(AXI_RDATA);
	endproperty
	AXI4_ERRS_RDATA_X_inst: assert property (AXI4_ERRS_RDATA_X);


	property AXI4_ERRS_RVALID_RESET; //RVALID is LOW for the first cycle after ARESETn goes HIGH.
		@(posedge AXI_ACLK)
			!AXI_ARESETN & !$isunknown(AXI_ARESETN)
			##1 AXI_ARESETN
			|-> !AXI_RVALID;
	endproperty
	AXI4_ERRS_RVALID_RESET_inst: assert property (AXI4_ERRS_RVALID_RESET);

	property AXI4_ERRS_RVALID_STABLE; //When RVALID is asserted, then it must remain asserted until RREADY is HIGH.
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_RVALID & !AXI_RREADY & !$isunknown({AXI_RVALID, AXI_RREADY})
			##1 AXI_ARESETN
			|-> AXI_RVALID;
	endproperty
	AXI4_ERRS_RVALID_STABLE_inst: assert property (AXI4_ERRS_RVALID_STABLE);


	property AXI4_ERRS_RVALID_X; //A value of X on RVALID is not permitted when not in reset.
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_RVALID});
	endproperty
	AXI4_ERRS_RVALID_X_inst: assert property (AXI4_ERRS_RVALID_X);

	property AXI4_ERRM_RREADY_X; //A value of X on RREADY is not permitted when not in reset.
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_RREADY});
	endproperty
	AXI4_ERRM_RREADY_X_inst: assert property (AXI4_ERRM_RREADY_X);


	property AXI4_RECM_RREADY_MAX_WAIT; //Recommended that RREADY is asserted within MAXWAITS cycles of RVALID being asserted.
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_RVALID & !AXI_RREADY & !$isunknown({AXI_RVALID, AXI_RREADY})
			|-> ##[1:maxwait] AXI_RREADY;
	endproperty
	AXI4_RECM_RREADY_MAX_WAIT_inst: assert property (AXI4_RECM_RREADY_MAX_WAIT);

endinterface: axic_rdata
