module axi4_assertion #(
    parameter DATA_WIDTH = 32,
    parameter ADDR_WIDTH = 16,
    parameter MEMORY_DEPTH = 1024
)(
    axi4_if.assert_mp axi
);

    // Common handshake sequences
    sequence aw_hs; axi.AWVALID && axi.AWREADY; endsequence
    sequence w_hs;  axi.WVALID && axi.WREADY;  endsequence
    sequence ar_hs; axi.ARVALID && axi.ARREADY; endsequence
    sequence r_hs;  axi.RVALID && axi.RREADY;  endsequence

    // VALID must remain asserted and control must remain stable until READY
    property aw_stable_until_ready;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        axi.AWVALID && !axi.AWREADY |=> $stable(axi.AWADDR) && $stable(axi.AWLEN) && $stable(axi.AWSIZE) && axi.AWVALID;
    endproperty
    assert_aw_stable_until_ready: assert property (aw_stable_until_ready);

    property ar_stable_until_ready;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        axi.ARVALID && !axi.ARREADY |=> $stable(axi.ARADDR) && $stable(axi.ARLEN) && $stable(axi.ARSIZE) && axi.ARVALID;
    endproperty
    assert_ar_stable_until_ready: assert property (ar_stable_until_ready);

    property w_stable_until_ready;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        axi.WVALID && !axi.WREADY |=> $stable(axi.WDATA) && $stable(axi.WLAST) && axi.WVALID;
    endproperty
    assert_w_stable_until_ready: assert property (w_stable_until_ready);

    // VALID should deassert after handshake completes (one beat transactions in this design)
    property awvalid_low_after_handshake;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        aw_hs |=> !axi.AWVALID;
    endproperty
    assert_awvalid_low_after_handshake: assert property (awvalid_low_after_handshake);

    // Response channels must hold VALID and payload until handshake
    property b_hold_until_ready;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        axi.BVALID && !axi.BREADY |=> $stable(axi.BRESP) && axi.BVALID;
    endproperty
    assert_b_hold_until_ready: assert property (b_hold_until_ready);

    property r_hold_until_ready;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        axi.RVALID && !axi.RREADY |=> $stable(axi.RDATA) && $stable(axi.RRESP) && $stable(axi.RLAST) && axi.RVALID;
    endproperty
    assert_r_hold_until_ready: assert property (r_hold_until_ready);

    // 4KB boundary must not be crossed within a burst (AXI requirement for a single transaction)
    property no_4kb_boundary_cross_on_aw;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        aw_hs |-> (((axi.AWADDR & 12'hFFF) + (axi.AWLEN << axi.AWSIZE)) <= 12'hFFF);
    endproperty
    assert_no_4kb_boundary_cross_on_aw: assert property (no_4kb_boundary_cross_on_aw);

    // Simple burst length tracking to validate WLAST and RLAST placement
    int unsigned w_beats_left;
    bit          w_active;
    int unsigned r_beats_left;
    bit          r_active;

    // Track write burst beats remaining
    always_ff @(posedge axi.ACLK or negedge axi.ARESETn) begin
        if (!axi.ARESETn) begin
            w_active      <= 1'b0;
            w_beats_left  <= '0;
        end else begin
            if (aw_hs) begin
                w_active     <= 1'b1;
                w_beats_left <= axi.AWLEN; // beats left after current (AWLEN is beats-1)
            end
            if (w_hs && w_active) begin
                if (w_beats_left == 0) begin
                    w_active <= 1'b0; // last beat consumed
                end else begin
                    w_beats_left <= w_beats_left - 1;
                end
            end
        end
    end

    // WLAST must assert only on the final data beat of a burst
    property wlast_only_on_final_beat;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        (w_hs && w_active && (w_beats_left != 0)) |-> !axi.WLAST;
    endproperty
    assert_wlast_only_on_final_beat: assert property (wlast_only_on_final_beat);

    property wlast_on_final_beat;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        (w_hs && w_active && (w_beats_left == 0)) |-> axi.WLAST;
    endproperty
    assert_wlast_on_final_beat: assert property (wlast_on_final_beat);

    // Track read burst beats remaining
    always_ff @(posedge axi.ACLK or negedge axi.ARESETn) begin
        if (!axi.ARESETn) begin
            r_active      <= 1'b0;
            r_beats_left  <= '0;
        end else begin
            if (ar_hs) begin
                r_active     <= 1'b1;
                r_beats_left <= axi.ARLEN; // beats left after current (ARLEN is beats-1)
            end
            if (r_hs && r_active) begin
                if (r_beats_left == 0) begin
                    r_active <= 1'b0; // last beat consumed
                end else begin
                    r_beats_left <= r_beats_left - 1;
                end
            end
        end
    end

    // RLAST must assert only on the final data beat of a burst
    property rlast_only_on_final_beat;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        (r_hs && r_active && (r_beats_left != 0)) |-> !axi.RLAST;
    endproperty
    assert_rlast_only_on_final_beat: assert property (rlast_only_on_final_beat);

    property rlast_on_final_beat;
        @(posedge axi.ACLK) disable iff (!axi.ARESETn)
        (r_hs && r_active && (r_beats_left == 0)) |-> axi.RLAST;
    endproperty
    assert_rlast_on_final_beat: assert property (rlast_on_final_beat);

    // Simple covers for visibility in GUI
    cover_aw_handshake: cover property (@(posedge axi.ACLK) disable iff (!axi.ARESETn) aw_hs);
    cover_ar_handshake: cover property (@(posedge axi.ACLK) disable iff (!axi.ARESETn) ar_hs);
    cover_b_handshake:  cover property (@(posedge axi.ACLK) disable iff (!axi.ARESETn) (axi.BVALID && axi.BREADY));
    cover_r_handshake:  cover property (@(posedge axi.ACLK) disable iff (!axi.ARESETn) r_hs);

endmodule