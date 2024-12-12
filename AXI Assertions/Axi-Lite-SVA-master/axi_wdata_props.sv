interface axic_wdata
	#(
		parameter integer maxwait = 5,
		parameter integer C_AXI_DATA_WIDTH = 32,
		parameter integer C_AXI_ADDR_WIDTH = 8
	)
	(
		input wire AXI_ACLK,
		input wire AXI_ARESETN,
		input wire[C_AXI_DATA_WIDTH-1:0] AXI_WDATA,
		input wire AXI_WVALID,
		input wire AXI_WREADY
	);

	property AXI4_ERRM_WDATA_STABLE; //WDATA remains stable when WVALID is asserted and WREADY is LOW.
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_WVALID & !AXI_WREADY & !$isunknown({AXI_WVALID, AXI_WREADY})
			##1 AXI_ARESETN
			|-> $stable(AXI_WDATA);
	endproperty
	AXI4_ERRM_WDATA_STABLE_inst: assert property (AXI4_ERRM_WDATA_STABLE);


	property AXI4_ERRM_WDATA_X; //A value of X on WDATA valid byte lanes is not permitted when WVALID is HIGH.
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_WVALID
			|-> !$isunknown(AXI_WDATA);
	endproperty
	AXI4_ERRM_WDATA_X_inst: assert property (AXI4_ERRM_WDATA_X);


	property AXI4_ERRM_WVALID_RESET; //WVALID is LOW for the first cycle after ARESETn goes HIGH.
		@(posedge AXI_ACLK)
			!AXI_ARESETN
			##1 AXI_ARESETN
			|-> !AXI_WVALID;
	endproperty
	AXI4_ERRM_WVALID_RESET_inst: assert property (AXI4_ERRM_WVALID_RESET);

	property AXI4_ERRM_WVALID_STABLE; //When WVALID is asserted, then it must remain asserted until WREADY is HIGH.
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_WVALID & !AXI_WREADY & !$isunknown({AXI_WVALID, AXI_WREADY})
			##1 AXI_ARESETN
			|-> AXI_WVALID;
	endproperty
	AXI4_ERRM_WVALID_STABLE_inst: assert property (AXI4_ERRM_WVALID_STABLE);


	property AXI4_ERRM_WVALID_X; //A value of X on WVALID is not permitted when not in reset.
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_WVALID});
	endproperty
	AXI4_ERRM_WVALID_X_inst: assert property (AXI4_ERRM_WVALID_X);

	property AXI4_ERRS_WREADY_X; //A value of X on WREADY is not permitted when not in reset.
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_WREADY});
	endproperty
	AXI4_ERRS_WREADY_X_inst: assert property (AXI4_ERRS_WREADY_X);


	property AXI4_RECS_WREADY_MAX_WAIT; //Recommended that WREADY is asserted within MAXWAITS cycles of WVALID being asserted.
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_WVALID & !AXI_WREADY & !$isunknown({AXI_WVALID, AXI_WREADY})
			|-> ##[1:maxwait] AXI_WREADY;
	endproperty
	AXI4_RECS_WREADY_MAX_WAIT_inst: assert property (AXI4_RECS_WREADY_MAX_WAIT);

endinterface: axic_wdata