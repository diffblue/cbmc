$! $Id: vms.com,v 1.1.1.1 2002-06-13 22:00:31 kroening Exp $ -*- dcl -*-
$!
$! Compile and run BigInt class with test code on VMS.
$! The VAX compiler seems to screw things up with optimization.
$!
$	if f$getsyi("arch_name") .eqs. "VAX"
$	then
$	    debug == /debug
$	    nodeb == /nodeb
$	    alloca == ",vax-alloca"
$	    macro vax-alloca.mar
$	endif
$	cxx'debug' bigint.cc,bigint-func.cc,bigint-test.cc
$	link'debug' bigint-test,bigint,bigint-func'alloca'
$	purge
$	run'nodeb' bigint-test
