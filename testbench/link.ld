
OUTPUT_ARCH( "riscv" )
ENTRY(_start)

SECTIONS
{
    . = 0x1000;
  .data .  : { *(.*data) *(.rodata*) }
  . = 0x0;
  .text .  : { *(.text) }
 _end = .;
}
