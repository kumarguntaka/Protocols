interface axic_raddr
	#(
		parameter integer maxwait = 5,
		parameter integer C_AXI_DATA_WIDTH = 32,
		parameter integer C_AXI_ADDR_WIDTH = 8
	)
	(
		input wire AXI_ACLK,
		input wire AXI_ARESETN,
		input wire[C_AXI_ADDR_WIDTH-1:0] AXI_ARADDR,
		input wire AXI_ARVALID,
		input wire AXI_ARREADY
	);


	property AXI4_ERRM_ARADDR_STABLE; // Wait for ARREADY
		@(posedge AXI_ACLK)
			!($isunknown({AXI_ARADDR, AXI_ARVALID, AXI_ARREADY})) &
			AXI_ARVALID & !AXI_ARREADY & AXI_ARESETN
			##1 AXI_ARESETN
			|-> $stable(AXI_ARADDR);
	endproperty
	AXI4_ERRM_ARADDR_STABLE_inst: assert property (AXI4_ERRM_ARADDR_STABLE);

	property AXI4_ERRM_ARADDR_X; // ARADDR should not be X and Z
		@(posedge AXI_ACLK)
			AXI_ARVALID & AXI_ARESETN
			|-> !$isunknown({AXI_ARADDR});
	endproperty
	AXI4_ERRM_ARADDR_X_inst: assert property (AXI4_ERRM_ARADDR_X);

	property AXI4_ERRM_ARVALID_RESET; // ARVALID is LOW for the first cycle after ARESETn goes HIGH
		@(posedge AXI_ACLK)
			!AXI_ARESETN & !$isunknown(AXI_ARESETN)
			##1 AXI_ARESETN // Doubt -> looks this should be (!AXI_ARESETN) because this should be high as per assertions doc.
			|-> !AXI_ARVALID;
	endproperty
	AXI4_ERRM_ARVALID_RESET_inst: assert property (AXI4_ERRM_ARVALID_RESET);


	property AXI4_ERRM_ARVALID_STABLE; //When ARVALID is asserted, then it remains asserted until ARREADY is HIGH
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_ARVALID & !AXI_ARREADY & !$isunknown({AXI_ARVALID, AXI_ARREADY})
			##1 AXI_ARESETN
			|-> AXI_ARVALID;
	endproperty
	AXI4_ERRM_ARVALID_STABLE_inst: assert property (AXI4_ERRM_ARVALID_STABLE);

	property AXI4_ERRM_ARVALID_X; //A value of X on ARVALID is not permitted when not in reset
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_ARVALID});
	endproperty
	AXI4_ERRM_ARVALID_X_inst: assert property (AXI4_ERRM_ARVALID_X);

	property AXI4_ERRS_ARREADY_X; //A value of X on ARREADY is not permitted when not in reset
		@(posedge AXI_ACLK)
			AXI_ARESETN
			|-> !$isunknown({AXI_ARREADY});
	endproperty
	AXI4_ERRS_ARREADY_X_inst: assert property (AXI4_ERRS_ARREADY_X);

	property AXI4_RECS_ARREADY_MAX_WAIT; // Recommended that ARREADY is asserted within MAXWAITS cycles of ARVALID being asserted 
		@(posedge AXI_ACLK)
			AXI_ARESETN & AXI_ARVALID & !AXI_ARREADY & !$isunknown({AXI_ARVALID, AXI_ARREADY})// Doubt with (!AXI_ARREADY).
			|-> ##[1:maxwait] AXI_ARREADY;
	endproperty
	AXI4_RECS_ARREADY_MAX_WAIT_inst: assert property (AXI4_RECS_ARREADY_MAX_WAIT);


endinterface: axic_raddr

