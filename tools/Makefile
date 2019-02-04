# SPDX-License-Identifier: Apache-2.0
# Copyright 2019 Western Digital Corporation or its affiliates.
# 
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
# 
# http://www.apache.org/licenses/LICENSE-2.0
# 
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Check for RV_ROOT
ifeq (,$(wildcard ${RV_ROOT}/configs/swerv.config))
$(error env var RV_ROOT does not point to a valid dir! Exiting!)
endif

# Allow snapshot override
ifeq ($(strip $(snapshot)),)
	snapshot = default
endif

defines = ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh ${RV_ROOT}/design/include/def.sv
includes = -I${RV_ROOT}/design/include -I${RV_ROOT}/design/lib -I${RV_ROOT}/design/dmi -I${RV_ROOT}/configs/snapshots/$(snapshot)
# CFLAGS for verilator generated Makefiles. Without -std=c++11 it complains for `auto` variables
CFLAGS += "-std=c++11"

all: clean verilator

clean:
	rm -rf obj_dir

verilator: ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh
	verilator '-UASSERT_ON' --cc -CFLAGS ${CFLAGS} $(defines) $(includes) ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh \
		-f ${RV_ROOT}/design/flist.verilator --top-module swerv_wrapper
	make -C obj_dir/ -f Vswerv_wrapper.mk

vcs: ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh
	vcs -full64 -assert svaext -sverilog +define+RV_OPENSOURCE +error+500 +incdir+${RV_ROOT}/design/lib +incdir+${RV_ROOT}/design/include \
		+incdir+${RV_ROOT}/design/dmi +incdir+${RV_ROOT}/configs/snapshots/$(snapshot)  +libext+.v ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh \
		${RV_ROOT}/design/include/def.sv -f ${RV_ROOT}/design/flist.vcs -l vcs.log

irun: ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh
	irun -64bit -elaborate -ida -access +rw -q -sv -sysv  -nowarn CUVIHR -nclibdirpath ${PWD} -nclibdirname swerv.build \
		-incdir ${RV_ROOT}/design/lib -incdir ${RV_ROOT}/design/include -incdir ${RV_ROOT}/design/dmi -vlog_ext +.vh\
		${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh ${RV_ROOT}/design/include/def.sv \
		-incdir ${RV_ROOT}/configs/snapshots/$(snapshot) -f ${RV_ROOT}/design/flist.vcs -elaborate  -snapshot default

${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh:
	${RV_ROOT}/configs/swerv.config -snapshot=$(snapshot)

verilator-run: 
	snapshot=ahb
	${RV_ROOT}/configs/swerv.config -snapshot=$(snapshot) -ahb
	verilator '-UASSERT_ON' --cc -CFLAGS ${CFLAGS} $(defines) $(includes) ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh \
		${RV_ROOT}/testbench/tb_top.sv -I${RV_ROOT}/testbench \
		-f ${RV_ROOT}/design/flist.verilator --top-module tb_top -exe test_tb_top.cpp --trace --autoflush
	cp ${RV_ROOT}/testbench/test_tb_top.cpp obj_dir/
	make -C obj_dir/ -f Vtb_top.mk
	cp ${RV_ROOT}/testbench/hex/*.hex .
	./obj_dir/Vtb_top

irun-run: 
	snapshot=ahb
	${RV_ROOT}/configs/swerv.config -snapshot=$(snapshot) -ahb
	cp ${RV_ROOT}/testbench/hex/*.hex .
	irun -64bit -ida -access +rw -q -sv -sysv  -nowarn CUVIHR -nclibdirpath ${PWD} -nclibdirname swerv.build \
		-incdir ${RV_ROOT}/design/lib -incdir ${RV_ROOT}/design/include -incdir ${RV_ROOT}/design/dmi -vlog_ext +.vh\
		${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh ${RV_ROOT}/design/include/def.sv \
		-top tb_top  ${RV_ROOT}/testbench/tb_top.sv -I${RV_ROOT}/testbench ${RV_ROOT}/testbench/ahb_sif.sv\
		-incdir ${RV_ROOT}/configs/snapshots/$(snapshot) -f ${RV_ROOT}/design/flist.vcs -snapshot default

vcs-run: ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh
	cp ${RV_ROOT}/testbench/hex/*.hex .
	vcs -full64 -assert svaext -sverilog +define+RV_OPENSOURCE +error+500 +incdir+${RV_ROOT}/design/lib +incdir+${RV_ROOT}/design/include \
		+incdir+${RV_ROOT}/design/dmi +incdir+${RV_ROOT}/configs/snapshots/$(snapshot)  +libext+.v ${RV_ROOT}/configs/snapshots/$(snapshot)/common_defines.vh \
		${RV_ROOT}/design/include/def.sv -f ${RV_ROOT}/design/flist.vcs ${RV_ROOT}/testbench/tb_top.sv -I${RV_ROOT}/testbench ${RV_ROOT}/testbench/ahb_sif.sv -l vcs.log
	./simv

help:
	@echo Make sure the environment variable RV_ROOT is set.
	@echo Possible targets: verilator vcs irun help clean all verilator-run irun-run vcs-run

.PHONY: help clean verilator vcs irun verilator-run irun-run  vcs-run
