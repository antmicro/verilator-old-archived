# Filenames starting with / to avoid false matches by suffix

VERILATOR_ONLY_SOURCE_FILENAMES=\
/sram_ctrl.sv \
/sram_ctrl_regs_reg_top.sv \
/kmac_pkg.sv \
/tl_main_pkg.sv \
/tl_peri_pkg.sv \
/top_earlgrey_rnd_cnst_pkg.sv \
/adc_ctrl_core.sv \
/clkmgr_byp.sv \
/clkmgr.sv \
/csrng_reg_top.sv \
/dmi_cdc.sv \
/edn_reg_top.sv \
/entropy_src_core.sv \
/entropy_src_reg_top.sv \
/entropy_src_watermark_reg.sv \
/flash_ctrl_core_reg_top.sv \
/flash_mp.sv \
/hmac_reg_top.sv \
/keccak_2share.sv \
/keccak_round.sv \
/keymgr_kmac_if.sv \
/keymgr_sideload_key_ctrl.sv \
/keymgr.sv \
/kmac_app.sv \
/kmac_core.sv \
/kmac_entropy.sv \
/kmac_errchk.sv \
/kmac_msgfifo.sv \
/kmac_reg_top.sv \
/kmac_staterd.sv \
/kmac.sv \
/lc_ctrl_fsm.sv \
/lc_ctrl_kmac_if.sv \
/otbn_reg_top.sv \
/otbn_rnd.sv \
/otbn.sv \
/otp_ctrl_core_reg_top.sv \
/otp_ctrl_part_buf.sv \
/otp_ctrl_scrmbl.sv \
/otp_ctrl.sv \
/pinmux_reg_top.sv \
/pinmux.sv \
/prim_dom_and_2share.sv \
/prim_fifo_async.sv \
/prim_generic_rom.sv \
/prim_present.sv \
/prim_ram_1p_scr.sv \
/prim_rom_adv.sv \
/prim_rom.sv \
/prim_slicer.sv \
/prim_subst_perm.sv \
/rom_ctrl_counter.sv \
/rom_ctrl_fsm.sv \
/rom_ctrl_mux.sv \
/rom_ctrl_scrambled_rom.sv \
/rom_ctrl.sv \
/rv_core_addr_trans.sv \
/rv_core_ibex_cfg_reg_top.sv \
/rv_core_ibex.sv \
/sha3pad.sv \
/sha3.sv \
/spi_device_reg_top.sv \
/spi_fwmode.sv \
/spi_host_data_cdc.sv \
/spi_host_reg_top.sv \
/spi_tpm.sv \
/tlul_fifo_async.sv \
/tlul_fifo_sync.sv \
/tlul_socket_1n.sv \
/tlul_socket_m1.sv \
/top_earlgrey.sv \
/uartdpi.sv \
/uart_reg_top.sv \
/usbdev_reg_top.sv \
/usbdev.sv \
/xbar_main.sv \
/xbar_peri.sv \

VERILATOR_AND_SURELOG_SOURCE_FILENAMES=\
/lc_ctrl.sv \
/keymgr_reg_top.sv \
/flash_ctrl.sv \
/rv_dm.sv \
/spi_device.sv \
/prim_ram_2p_async_adv.sv \
/aes_ctrl_reg_shadowed.sv \
/alert_handler_reg_top.sv \
/edn_core.sv \
/csrng_core.sv \
/flash_mp_data_region_sel.sv \
/usbdev_aon_wake.sv \
/sensor_ctrl_reg_top.sv \
/rv_timer.sv \
/rv_timer_reg_top.sv \
/rv_plic_target.sv \
/prim_packer.sv \
/prim_arbiter_ppc.sv \
/pinmux.sv \
/pinmux_strap_sampling.sv \
/pattgen.sv \
/gpio.sv \
/flash_phy.sv \
/entropy_src.sv \
/ast_dft.sv \
/aon_timer.sv \
/adc_ctrl_reg_top.sv \
/adc_ctrl_intr.sv \
/uart_core.sv \
/uart.sv \
/sensor_ctrl.sv \
/spi_host.sv \
/prim_edn_req.sv \
/hmac.sv \
/i2c.sv \
/edn.sv \
/csrng.sv \
/clkmgr_reg_top.sv \
/ast_reg_top.sv \
/ast.sv \
/aon_timer_reg_top.sv \
/alert_handler.sv \
/aes.sv \
/aes_reg_top.sv \
/prim_esc_sender.sv \
/prim_esc_receiver.sv \
/sysrst_ctrl.sv \
/sysrst_ctrl_reg_top.sv \
/sys_osc.sv \
/sys_clk.sv \
/prim_clock_meas.sv \
/prim_clock_gating_sync.sv \
/prim_clock_div.sv \
/rv_plic.sv \
/rv_plic_reg_top.sv \
/rv_dm_regs_reg_top.sv \
/rstmgr.sv \
/rstmgr_reg_top.sv \
/rstmgr_por.sv \
/rstmgr_ctrl.sv \
/rom_ctrl_regs_reg_top.sv \
/pwrmgr.sv \
/pwrmgr_reg_top.sv \
/pwm.sv \
/pwm_reg_top.sv \
/prim_sram_arbiter.sv \
/prim_reg_cdc.sv \
/prim_lc_sync.sv \
/usb_osc.sv \
/usbdev_linkstate.sv \
/usbdev_iomux.sv \
/usb_clk.sv \
/prim_alert_sender.sv \
/prim_alert_receiver.sv \
/pinmux_wkup.sv \
/pinmux_jtag_buf.sv \
/pattgen_reg_top.sv \
/pattgen_core.sv \
/otbn_stack_snooper_if.sv \
/otbn_rf_snooper_if.sv \
/otbn_rf_base.sv \
/otbn_core_model.sv \
/lc_ctrl_reg_top.sv \
/io_osc.sv \
/io_clk.sv \
/i2c_reg_top.sv \
/i2c_core.sv \
/gpio_reg_top.sv \
/aon_osc.sv \
/tlul_sram_byte.sv \
/tlul_assert_multiple.sv \
/tlul_adapter_sram.sv \
/spi_s2p.sv \
/prim_sync_reqack_data.sv \
/prim_subreg_arb.sv \
/usb_fs_tx.sv \
/tlul_rsp_intg_gen.sv \
/tlul_cmd_intg_gen.sv \
/tlul_adapter_reg.sv \
/spi_host_byte_merge.sv \
/spi_fwm_txf_ctrl.sv \
/spid_status.sv \
/prim_subreg.sv \
/prim_ram_1p_adv.sv \
/prim_generic_flop_2sync.sv \
/prim_fifo_sync.sv \
/prim_count.sv \
/prim_arbiter_tree.sv \
/prim_arbiter_fixed.sv \
/otbn_stack.sv \
/aes_sel_buf_chk.sv \
/aes_prng_masking.sv \
/prim_prince.sv \
/prim_packer_fifo.sv \
/prim_lfsr.sv \
/prim_generic_flop.sv \
/prim_generic_buf.sv \
/prim_flop.sv \
/prim_flop_2sync.sv \
/prim_buf.sv \
/otp_ctrl_ecc_reg.sv \
/aes_cipher_control.sv \
/aes_cipher_core.sv \
/prim_intr_hw.sv \
/prim_filter.sv \
/aes_sbox.sv \
/prim_clock_mux2.sv \
/prim_generic_clock_mux2.sv \
/prim_clock_inv.sv \
/prim_generic_clock_inv.sv \
/prim_diff_decode.sv \
/prim_clock_buf.sv \
/prim_generic_clock_buf.sv \
/prim_clock_gating.sv \
/prim_generic_clock_gating.sv \
/prim_subreg_ext.sv \
/prim_subreg_shadow.sv \
/prim_edge_detector.sv \
/prim_ram_2p.sv \
/tlul_adapter_host.sv \
/prim_generic_ram_2p.sv \
/prim_flash.sv \
/prim_generic_flash_bank.sv \
/prim_generic_flash.sv \
/tlul_err.sv \
/prim_generic_ram_1p.sv \
/prim_ram_1p.sv \
