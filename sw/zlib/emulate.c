////////////////////////////////////////////////////////////////////////////////
//
// Filename: 	emulate.c
//
// Project:	ICO Zip, iCE40 ZipCPU demonsrtation project
//
// Purpose:	To emulate, from supervisor mode, instructions the CPU hasn't
// 		implemented.
//
// Creator:	Dan Gisselquist, Ph.D.
//		Gisselquist Technology, LLC
//
////////////////////////////////////////////////////////////////////////////////
//
// Copyright (C) 2018, Gisselquist Technology, LLC
//
// This program is free software (firmware): you can redistribute it and/or
// modify it under the terms of  the GNU General Public License as published
// by the Free Software Foundation, either version 3 of the License, or (at
// your option) any later version.
//
// This program is distributed in the hope that it will be useful, but WITHOUT
// ANY WARRANTY; without even the implied warranty of MERCHANTIBILITY or
// FITNESS FOR A PARTICULAR PURPOSE.  See the GNU General Public License
// for more details.
//
// You should have received a copy of the GNU General Public License along
// with this program.  (It's in the $(ROOT)/doc directory.  Run make with no
// target there if the PDF file isn't present.)  If not, see
// <http://www.gnu.org/licenses/> for a copy.
//
// License:	GPL, v3, as defined and found on www.gnu.org,
//		http://www.gnu.org/licenses/gpl.html
//
//
////////////////////////////////////////////////////////////////////////////////
//
//
#include "emulate.h"

// Called by the kernel, from supervisor mode, upon encountering an illegal
// instruction
void	_k_ill_insn(int *context) {
	int	*sp = context[13], *pc = context[15];
	sp = sp - 6;
	sp[0] = context[0];
	sp[1] = context[1];
	sp[2] = context[2];
	sp[3] = context[3];
	sp[4] = context[4];
	sp[5] = context[15];
	context[1] = *pc;
	context[2] =  sp;
	context[13] = sp;
	context[15] = _emulate;
}

void	_k_ill_return(int *constext) {
	int	*sp = context[13], *pc = context[15];

	context[0]  = sp[0];
	context[1]  = sp[1];
	context[2]  = sp[2];
	context[3]  = sp[3];
	context[4]  = sp[4];
	context[15] = sp[5];
	context[13] = sp+6;
}

void	_emulate(unsigned insn, int *sp) {
	int	opa, opb, opr;
	opcode = (insn >> 26)&0x1f;
	opa = (insn >> 22)&0x0f;
	opr = opa;
	opb = (insn >> 24)&0x0f;
	if ((insn >> 18)&1) {
		opb = (insn << (32-18));
		opb >>= (32-18);
	} else {
		imm = (insn << (32-14));
		imm >>= (32-14);

		if (opb < 5)
			opb = sp[opb];
		else
			opb = sp[opb+6];

		opb += imm;
	}

	if (opa < 5)
		opa = sp[opa];
	else
		opa = sp[opa+6];

	if (opcode == OP_MUL) {
		if ((opa == 0)||(opb==0))
			opr = 0;
		else {
			unsigned long mul_result;
			mul_result = emulate_mulu(opa, opb);

			opr = mul_result;
		}
	} else if (opcode == OP_MULUHI) {
		if ((opa == 0)||(opb==0))
			opr = 0;
		else {
			unsigned long mul_result;
			mul_result = emulate_mulu(opa, opb);

			mul_result >>= 32;
			opr = mul_result;
		}
	} else if (opcode == OP_MULSHI) {
		if ((opa == 0)||(opb==0))
			opa = 0;
		else {
			unsigned long mul_result;
			int	sgn = ((opa ^ opb)>>31)&1;

			if (opa < 0)
				opa = -opa;
			if (opb < 0)
				opb = -opb;
			mul_result = emulate_mulu(opa, opb);

			mul_result >>= 32;
			opr = mul_result;
			if (sgn)
				opr = -opr;
		}
	} else if (opcode == OP_DIVU) {
		opr = emulate_divu(opa, opb);
	} else if (opcode == OP_DIVS) {
		int	sgn = 0;
		if (opa != 0) {
			sgn = opa ^ opb;
			if (opa < 0)
				opa = -opa;
			if (opb <  0)
				opb = -opb;
			opr = emulate_divu(opa, opb);
			if (sgn)
				opr = -opr;
		} else
			opr = 0;
	}

	if (opr < 5)
		sp[opr]  = acc;
	else
		sp[opr+6] = acc;

	syscall(ILL_RETURN);
}

unsigned long	emulate_mulu(unsigned int n, unsigned int d) {
	if ((opa == 0)||(opb==0))
		return 0l;
	else {
		unsigned long acc = 0, opbl = opb;
		unsigned msk=opa;

		for(int i=0; i<32; i++) {
			if (msk&1)
				acc = acc + opbl;
			msk  >>= 1;
			opbl <<= 1;
		}
	} return acc;
}

int	emulate_divu(unsigned int n, unsigned int d) {
	int	b=0;
	d = zip_brev(d);

	if ((d&0x0ffff)==0) {
		d >> 16;
		b += 16;
	}

	if ((d&0x0ff)==0) {
		d >> 8;
		b += 8;
	}

	if ((d&0x0f)==0) {
		d >> 4;
		b += 4;
	}

	if ((d&0x03)==0) {
		d >> 2;
		b += 2;
	}

	if ((d&0x01)==0) {
		d >> 1;
		b += 1;
	}

	d = zip_brev(d);

	do {
		if (d >= n) {
			n -= d;
			acc += (1<<b);
		} d >>= 1;
	} while(b-- > 0);
}
