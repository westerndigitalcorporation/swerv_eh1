# SweRV RISC-V Core<sup>TM</sup> 1.1 from Western Digital
## Release Notes
1. SWERV core RISCV compatibility improvements

    * Illegal instructions no longer increment minstret
    * Debug single-step command no longer executes multiple instructions
    * For instructions, MTVAL register holds the address that actually
      triggered an access fault
    * DICAD1 debug CSR ECC read size enhancements

1. SWERV core performance enhancements

    * Improved instruction fetch unit external memory access performance
    * Instruction fetcher no longer stalls due to DMA ICCM requests
    * Improved performance of streaming stores
    * Improved performance of divide instruction
    * Improved I/O Timing 
    * Non-idempotent Ld/St changed to non-posted in MFDC
    * DMA QoS Configurable in MFDC

1. SWERV core miscellaneous changes

    * Non-word access to PIC memory generates access-error
    * Improved streaming performance with unified read/write buffer
    * Non-idempotent load enhancements
    * Debug, single-step, and trigger enhancements
    * DMA, IFU, and LSU interaction enhancements
    * Bus error handling improvements
    * DMA h-ready addition
    * DMA slave error response enhancements

1. Added memory protection regions
    
	* Now able to define up to eight instruction fetch windows and up to eight
	  data load/store windows. See the programmer reference manual for more
	  details.
