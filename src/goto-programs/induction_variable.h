/*
 * induction_variable.h
 *
 *  Created on: August 18, 2010
 *      Author: Alastair Donaldson
 */

#ifndef INDUCTION_VARIABLE_H_
#define INDUCTION_VARIABLE_H_

class induction_variablet /* Represents simple induction variables */
{
	induction_variablet(symbolt induction_variable, exprt lower_bound, exprt upper_bound, exprt step) :
		induction_variable(induction_variable), lower_bound(lower_bound), upper_bound(upper_bound), step(step)
	{

	}


private:
	symbolt induction_variable;
	exprt lower_bound;
	exprt upper_bound;
	exprt step;
};

#endif
