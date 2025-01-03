interface axic_wresp
	#(
		parameter integer maxwait = 5,
		parameter integer C_AXI_DATA_WIDTH = 32,
		parameter integer C_AXI_ADDR_WIDTH = 8
	)
	(
		input wire AXI_ACLK,
		input wire AXI_ARESETN,
		input wire[1:0] AXI_BRESP,
		input wire AXI_BVALID,
		input wire AXI_BREADY
	);

	property AXI4_ERRS_BRESP_STABLE; //BRESP remains stable when BVALID is asserted and BREADY is LOW
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_BVALID & !AXI_BREADY & !$isunknown({AXI_BVALID, AXI_BREADY, AXI_BRESP})
			##1 AXI_ARESETN
			|-> $stable(AXI_BRESP);
	endproperty
	AXI4_ERRS_BRESP_STABLE_inst: assert property (AXI4_ERRS_BRESP_STABLE);

	property AXI4_ERRS_BRESP_X; //A value of X on BRESP is not permitted when BVALID is HIGH
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_BVALID
			|-> !$isunknown(AXI_BRESP);
	endproperty
	AXI4_ERRS_BRESP_X_inst: assert property (AXI4_ERRS_BRESP_X);

	property AXI4_ERRS_BVALID_RESET; //BVALID is LOW for the first cycle after ARESETn goes HIGH
		@(posedge AXI_ACLK)
			!AXI_ARESETN
			##1 AXI_ARESETN
			|-> !AXI_BVALID;
	endproperty
	AXI4_ERRS_BVALID_RESET_inst: assert property (AXI4_ERRS_BVALID_RESET);

	property AXI4_ERRS_BVALID_STABLE; //When BVALID is asserted, then it must remain asserted until BREADY is HIGH
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_BVALID & !AXI_BREADY & !$isunknown({AXI_BVALID, AXI_BREADY})
			##1 AXI_ARESETN
			|-> AXI_BVALID;
	endproperty
	AXI4_ERRS_BVALID_STABLE_inst: assert property (AXI4_ERRS_BVALID_STABLE);

	property AXI4_ERRS_BVALID_X; //A value of X on BVALID is not permitted when not in reset
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_BVALID});
	endproperty
	AXI4_ERRS_BVALID_X_inst: assert property (AXI4_ERRS_BVALID_X);

	property AXI4_ERRM_BREADY_X; //A value of X on BREADY is not permitted when not in reset
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_BREADY});
	endproperty
	AXI4_ERRM_BREADY_X_inst: assert property (AXI4_ERRM_BREADY_X);


	property AXI4_RECM_BREADY_MAX_WAIT; //Recommended that BREADY is asserted within MAXWAITS cycles of BVALID being asserted
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_BVALID & !AXI_BREADY & !$isunknown({AXI_BVALID, AXI_BREADY})
			|-> ##[1:maxwait] AXI_BREADY;
	endproperty
	AXI4_RECM_BREADY_MAX_WAIT_inst: assert property (AXI4_RECM_BREADY_MAX_WAIT);

endinterface: axic_wresp