#include <assert.h>

// C semantics are that these will be zero
// Easy to represent as ID_array_of
int uninitialisedGlobalArray1 [256];
int uninitialisedGlobalArray2 [256];

// Harder but possible to be ID_array_of
int initialisedUniform1 [] = {
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0
};

int initialisedUniform2 [] = {
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0,
  0, 0, 0, 0, 0, 0, 0, 0,  0, 0, 0, 0, 0, 0, 0, 0
};

int initialisedUniform3 [] = {
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 1, 1, 1,
  1, 1, 1, 1, 1, 1, 1, 1,  1, 1, 1, 1, 1, 1, 1, 1
};

// Can't be represented as array_of
int initialisedNonUniform1 [] = {
  0x0, 0x1, 0x2, 0x3,
  0x4, 0x5, 0x6, 0x7,
  0x8, 0x9, 0xA, 0xB,
  0xC, 0xD, 0xE, 0xF
};

int initialisedNonUniform2 [] = {
  0x0, 0x1, 0x2, 0x3,
  0x4, 0x5, 0x6, 0x7,
  0x8, 0x9, 0xA, 0xB,
  0xC, 0xD, 0xE, 0xF
};

int initialisedNonUniform3 [] = {
  0xF, 0xE, 0xD, 0xC,
  0xB, 0xA, 0x9, 0x8,
  0x7, 0x6, 0x5, 0x4,
  0x3, 0x2, 0x1, 0x0,
};

int nondet_int (void);


int main (void) {

  int test = nondet_int();

  if (test == 0) {

    /*** Direct use ***/
    // No changes

    // Constant accesss : should simplify away
    assert(uninitialisedGlobalArray1[31] == 0);
    assert(uninitialisedGlobalArray1[23] == 0);
    assert(uninitialisedGlobalArray2[37] == 0);

    assert(initialisedUniform1[11] == 0);
    assert(initialisedUniform2[13] == 0);
    assert(initialisedUniform2[15] == 0);
    assert(initialisedUniform3[17] == 1);

    assert(initialisedNonUniform1[3] == 3);
    assert(initialisedNonUniform1[5] == 5);
    assert(initialisedNonUniform2[7] == 7);
    assert(initialisedNonUniform3[9] == 6);

    // Variable access
    int directUseReadLocation[8]; // Non-det

    if (0 <= directUseReadLocation[0] &&
	directUseReadLocation[0] < 256)
      assert(uninitialisedGlobalArray1[directUseReadLocation[0]] == 0);
    if (0 <= directUseReadLocation[1] &&
	directUseReadLocation[1] < 256)
      assert(uninitialisedGlobalArray2[directUseReadLocation[1]] == 0);

    if (0 <= directUseReadLocation[2] &&
	directUseReadLocation[2] < 64)
      assert(initialisedUniform1[directUseReadLocation[2]] == 0);
    if (0 <= directUseReadLocation[3] &&
	directUseReadLocation[3] < 64)
      assert(initialisedUniform2[directUseReadLocation[3]] == 0);
    if (0 <= directUseReadLocation[4] &&
	directUseReadLocation[4] < 64)
      assert(initialisedUniform3[directUseReadLocation[4]] == 1);

    if (0 <= directUseReadLocation[5] &&
	directUseReadLocation[5] < 16)
      assert(initialisedNonUniform1[directUseReadLocation[5]] == directUseReadLocation[5]);
    if (0 <= directUseReadLocation[6] &&
	directUseReadLocation[6] < 16)
      assert(initialisedNonUniform2[directUseReadLocation[6]] == directUseReadLocation[6]);
    if (0 <= directUseReadLocation[7] &&
	directUseReadLocation[7] < 16)
      assert(initialisedNonUniform3[directUseReadLocation[7]] == 15 - directUseReadLocation[7]);


  } else if (test == 1) {

    /*** Constant redundant update ***/
    // Updates should simplify away.
    // Shouldn't require array_of to array conversion.

    uninitialisedGlobalArray1[2] = 0;
    uninitialisedGlobalArray1[23] = 0;
    uninitialisedGlobalArray1[33] = 0;
    uninitialisedGlobalArray2[63] = 0;

    initialisedUniform1[13] = 0;
    initialisedUniform2[11] = 0;
    initialisedUniform2[15] = 0;
    initialisedUniform3[11] = 1;
    initialisedUniform3[13] = 1;
    initialisedUniform3[15] = 1;
    initialisedUniform3[17] = 1;

    // These two check write re-ordering and coalescing
    initialisedNonUniform1[2] = 11;
    initialisedNonUniform1[3] = 25;

    initialisedNonUniform1[2] = 2;
    initialisedNonUniform1[3] = 3;
    initialisedNonUniform1[4] = 4;
    initialisedNonUniform2[4] = 4;
    initialisedNonUniform3[9] = 6;
    initialisedNonUniform3[7] = 8;

    // Constant accesss : should simplify away
    assert(uninitialisedGlobalArray1[31] == 0);
    assert(uninitialisedGlobalArray1[23] == 0);
    assert(uninitialisedGlobalArray2[37] == 0);

    assert(initialisedUniform1[11] == 0);
    assert(initialisedUniform2[13] == 0);
    assert(initialisedUniform2[15] == 0);
    assert(initialisedUniform3[17] == 1);

    assert(initialisedNonUniform1[3] == 3);
    assert(initialisedNonUniform1[5] == 5);
    assert(initialisedNonUniform2[7] == 7);
    assert(initialisedNonUniform3[9] == 6);

    // Variable access
    int constantRedundantUpdateReadLocation[8]; // Non-det

    if (0 <= constantRedundantUpdateReadLocation[0] &&
	constantRedundantUpdateReadLocation[0] < 256)
      assert(uninitialisedGlobalArray1[constantRedundantUpdateReadLocation[0]] == 0);
    if (0 <= constantRedundantUpdateReadLocation[1] &&
	constantRedundantUpdateReadLocation[1] < 256)
      assert(uninitialisedGlobalArray2[constantRedundantUpdateReadLocation[1]] == 0);

    if (0 <= constantRedundantUpdateReadLocation[2] &&
	constantRedundantUpdateReadLocation[2] < 64)
      assert(initialisedUniform1[constantRedundantUpdateReadLocation[2]] == 0);
    if (0 <= constantRedundantUpdateReadLocation[3] &&
	constantRedundantUpdateReadLocation[3] < 64)
      assert(initialisedUniform2[constantRedundantUpdateReadLocation[3]] == 0);
    if (0 <= constantRedundantUpdateReadLocation[4] &&
	constantRedundantUpdateReadLocation[4] < 64)
      assert(initialisedUniform3[constantRedundantUpdateReadLocation[4]] == 1);

    if (0 <= constantRedundantUpdateReadLocation[5] &&
	constantRedundantUpdateReadLocation[5] < 16)
      assert(initialisedNonUniform1[constantRedundantUpdateReadLocation[5]] == constantRedundantUpdateReadLocation[5]);
    if (0 <= constantRedundantUpdateReadLocation[6] &&
	constantRedundantUpdateReadLocation[6] < 16)
      assert(initialisedNonUniform2[constantRedundantUpdateReadLocation[6]] == constantRedundantUpdateReadLocation[6]);
    if (0 <= constantRedundantUpdateReadLocation[7] &&
	constantRedundantUpdateReadLocation[7] < 16)
      assert(initialisedNonUniform3[constantRedundantUpdateReadLocation[7]] == 15 - constantRedundantUpdateReadLocation[7]);


  } else if (test == 2) {

    /*** Constant non-redundant update ***/
    // Simplification will likely need to convert array_of to array
    uninitialisedGlobalArray1[5] = 1;
    uninitialisedGlobalArray1[23] = 2;
    uninitialisedGlobalArray1[53] = 3;
    uninitialisedGlobalArray2[62] = 4;

    initialisedUniform1[12] = 1;
    initialisedUniform2[10] = 1;
    initialisedUniform2[15] = 1;
    initialisedUniform3[11] = 0;
    initialisedUniform3[13] = 0;
    initialisedUniform3[15] = 0;
    initialisedUniform3[17] = 0;

    initialisedNonUniform1[2] = -2;
    initialisedNonUniform1[3] = -3;
    initialisedNonUniform1[7] = -4;
    initialisedNonUniform2[3] = 11;
    initialisedNonUniform3[9] = 11;
    initialisedNonUniform3[7] = 10;



    // Constant accesss : should still simplify away
    assert(uninitialisedGlobalArray1[31] == 0);
    assert(uninitialisedGlobalArray1[23] == 2);
    assert(uninitialisedGlobalArray2[37] == 0);

    assert(initialisedUniform1[11] == 0);
    assert(initialisedUniform2[13] == 0);
    assert(initialisedUniform2[15] == 1);
    assert(initialisedUniform3[17] == 0);

    assert(initialisedNonUniform1[3] == -3);
    assert(initialisedNonUniform1[5] == 5);
    assert(initialisedNonUniform2[7] == 7);
    assert(initialisedNonUniform3[9] == 11);

    // Variable access
    int constantNonRedundantUpdateReadLocation[8]; // Non-det

    if (0 <= constantNonRedundantUpdateReadLocation[0] &&
	constantNonRedundantUpdateReadLocation[0] < 5)
      assert(uninitialisedGlobalArray1[constantNonRedundantUpdateReadLocation[0]] == 0);
    if (0 <= constantNonRedundantUpdateReadLocation[1] &&
	constantNonRedundantUpdateReadLocation[1] < 62)
      assert(uninitialisedGlobalArray2[constantNonRedundantUpdateReadLocation[1]] == 0);

    if (0 <= constantNonRedundantUpdateReadLocation[2] &&
	constantNonRedundantUpdateReadLocation[2] < 64 &&
	constantNonRedundantUpdateReadLocation[2] != 12)
      assert(initialisedUniform1[constantNonRedundantUpdateReadLocation[2]] == 0);
    if (16 <= constantNonRedundantUpdateReadLocation[3] &&
	constantNonRedundantUpdateReadLocation[3] < 64)
      assert(initialisedUniform2[constantNonRedundantUpdateReadLocation[3]] == 0);
    if (0 <= constantNonRedundantUpdateReadLocation[4] &&
	constantNonRedundantUpdateReadLocation[4] < 64 &&
	(constantNonRedundantUpdateReadLocation[4] & 0x1) == 0)
      assert(initialisedUniform3[constantNonRedundantUpdateReadLocation[4]] == 1);

    if (8 <= constantNonRedundantUpdateReadLocation[5] &&
	constantNonRedundantUpdateReadLocation[5] < 16)
      assert(initialisedNonUniform1[constantNonRedundantUpdateReadLocation[5]] == constantNonRedundantUpdateReadLocation[5]);
    if (0 <= constantNonRedundantUpdateReadLocation[6] &&
	constantNonRedundantUpdateReadLocation[6] < 16 &&
	constantNonRedundantUpdateReadLocation[6] != 3)
      assert(initialisedNonUniform2[constantNonRedundantUpdateReadLocation[6]] == constantNonRedundantUpdateReadLocation[6]);
    if (0 <= constantNonRedundantUpdateReadLocation[7] &&
	constantNonRedundantUpdateReadLocation[7] < 9 &&
	constantNonRedundantUpdateReadLocation[7] != 7)
      assert(initialisedNonUniform3[constantNonRedundantUpdateReadLocation[7]] == 15 - constantNonRedundantUpdateReadLocation[7]);


  } else if (test == 3) {

    /*** Variable redundant update ***/
    // In theory the writes might be simplifable but :
    // * If bounded then we need to use information about the ranges
    //   of the write location which are inaccessible in a
    //   context-free rewriter.
    // * For the non-uniform arrays some complex reasoning is needed.
    // * Simplification across Phi nodes is needed as well

    int redundantWriteLocation[16];

    if (0 <= redundantWriteLocation[0] &&
	redundantWriteLocation[0] < 256)
      uninitialisedGlobalArray1[redundantWriteLocation[0]] = 0;

    if (0 <= redundantWriteLocation[1] &&
	redundantWriteLocation[1] < 256)
      uninitialisedGlobalArray1[redundantWriteLocation[1]] = 0;

    if (0 <= redundantWriteLocation[2] &&
	redundantWriteLocation[2] < 256)
      uninitialisedGlobalArray2[redundantWriteLocation[2]] = 0;



    if (0 <= redundantWriteLocation[3] &&
	redundantWriteLocation[3] < 64)
      initialisedUniform1[redundantWriteLocation[3]] = 0;

    if (0 <= redundantWriteLocation[4] &&
	redundantWriteLocation[4] < 64)
      initialisedUniform2[redundantWriteLocation[4]] = 0;

    if (0 <= redundantWriteLocation[5] &&
	redundantWriteLocation[5] < 64)
      initialisedUniform2[redundantWriteLocation[5]] = 0;

    if (0 <= redundantWriteLocation[6] &&
	redundantWriteLocation[6] < 64)
      initialisedUniform3[redundantWriteLocation[6]] = 1;

    if (0 <= redundantWriteLocation[7] &&
	redundantWriteLocation[7] < 64)
      initialisedUniform3[redundantWriteLocation[7]] = 1;

    if (0 <= redundantWriteLocation[8] &&
	redundantWriteLocation[8] < 64)
      initialisedUniform3[redundantWriteLocation[8]] = 1;

    if (0 <= redundantWriteLocation[9] &&
	redundantWriteLocation[9] < 64)
      initialisedUniform3[redundantWriteLocation[9]] = 1;


    if ((0 <= redundantWriteLocation[10] &&
	 redundantWriteLocation[10] < 16) &&
	(0 <= redundantWriteLocation[11] &&
	 redundantWriteLocation[11] < 16) &&
	(0 <= redundantWriteLocation[12] &&
	 redundantWriteLocation[12] < 16)) {
      // Check write coallescing and reordering
      // Can re-order writes if the indexes being equal implies the
      // values are equal.

      initialisedNonUniform1[redundantWriteLocation[10]] = 29;
      initialisedNonUniform1[redundantWriteLocation[11]] = 29;

      initialisedNonUniform1[redundantWriteLocation[10]] = redundantWriteLocation[10];
      initialisedNonUniform1[redundantWriteLocation[11]] = redundantWriteLocation[11];
      initialisedNonUniform1[redundantWriteLocation[12]] = redundantWriteLocation[12];
    }

    if ((0 <= redundantWriteLocation[13] &&
	 redundantWriteLocation[13] < 16)) {
      initialisedNonUniform2[redundantWriteLocation[13]] = redundantWriteLocation[13];
    }

    if ((0 <= redundantWriteLocation[14] &&
	 redundantWriteLocation[14] < 16)) {
      initialisedNonUniform3[redundantWriteLocation[14]] = 15 - redundantWriteLocation[14];
    }
    if ((0 <= redundantWriteLocation[15] &&
	 redundantWriteLocation[15] < 16)) {
      initialisedNonUniform3[redundantWriteLocation[15]] = 15 - redundantWriteLocation[15];
    }


    // Constant access
    // If the array is simplified then this should simplify as well
    // If not then they likely won't and thus an example of a constant
    // index into a non-constant (but completely known) array.


    assert(uninitialisedGlobalArray1[31] == 0);
    assert(uninitialisedGlobalArray1[23] == 0);
    assert(uninitialisedGlobalArray2[37] == 0);

    assert(initialisedUniform1[11] == 0);
    assert(initialisedUniform2[13] == 0);
    assert(initialisedUniform2[15] == 0);
    assert(initialisedUniform3[17] == 1);

    assert(initialisedNonUniform1[3] == 3);
    assert(initialisedNonUniform1[5] == 5);
    assert(initialisedNonUniform2[7] == 7);
    assert(initialisedNonUniform3[9] == 6);


    // Variable access
    int variableRedundantUpdateReadLocation[8]; // Non-det

    if (0 <= variableRedundantUpdateReadLocation[0] &&
	variableRedundantUpdateReadLocation[0] < 256)
      assert(uninitialisedGlobalArray1[variableRedundantUpdateReadLocation[0]] == 0);
    if (0 <= variableRedundantUpdateReadLocation[1] &&
	variableRedundantUpdateReadLocation[1] < 256)
      assert(uninitialisedGlobalArray2[variableRedundantUpdateReadLocation[1]] == 0);

    if (0 <= variableRedundantUpdateReadLocation[2] &&
	variableRedundantUpdateReadLocation[2] < 64)
      assert(initialisedUniform1[variableRedundantUpdateReadLocation[2]] == 0);
    if (0 <= variableRedundantUpdateReadLocation[3] &&
	variableRedundantUpdateReadLocation[3] < 64)
      assert(initialisedUniform2[variableRedundantUpdateReadLocation[3]] == 0);
    if (0 <= variableRedundantUpdateReadLocation[4] &&
	variableRedundantUpdateReadLocation[4] < 64)
      assert(initialisedUniform3[variableRedundantUpdateReadLocation[4]] == 1);

    if (0 <= variableRedundantUpdateReadLocation[5] &&
	variableRedundantUpdateReadLocation[5] < 16)
      assert(initialisedNonUniform1[variableRedundantUpdateReadLocation[5]] == variableRedundantUpdateReadLocation[5]);
    if (0 <= variableRedundantUpdateReadLocation[6] &&
	variableRedundantUpdateReadLocation[6] < 16)
      assert(initialisedNonUniform2[variableRedundantUpdateReadLocation[6]] == variableRedundantUpdateReadLocation[6]);
    if (0 <= variableRedundantUpdateReadLocation[7] &&
	variableRedundantUpdateReadLocation[7] < 16)
      assert(initialisedNonUniform3[variableRedundantUpdateReadLocation[7]] == 15 - variableRedundantUpdateReadLocation[7]);


  } else if (test == 4) {

    /*** Variable non-redundant update ***/
    // No obvious simplifications to writes

    int nonRedundantWriteLocation[16];

    if (0 <= nonRedundantWriteLocation[0] &&
	nonRedundantWriteLocation[0] < 256 &&
	nonRedundantWriteLocation[0] != 31)
      uninitialisedGlobalArray1[nonRedundantWriteLocation[0]] = 1;

    if (0 <= nonRedundantWriteLocation[1] &&
	nonRedundantWriteLocation[1] < 256 &&
	nonRedundantWriteLocation[1] != 31 &&
	nonRedundantWriteLocation[1] != 23)
      uninitialisedGlobalArray1[nonRedundantWriteLocation[1]] = nonRedundantWriteLocation[1];

    if (0 <= nonRedundantWriteLocation[2] &&
	nonRedundantWriteLocation[2] < 256)
      uninitialisedGlobalArray2[nonRedundantWriteLocation[2]] = (nonRedundantWriteLocation[2] & 0xFF);



    if (0 <= nonRedundantWriteLocation[3] &&
	nonRedundantWriteLocation[3] < 10)
      initialisedUniform1[nonRedundantWriteLocation[3]] = 1;

    if (0 <= nonRedundantWriteLocation[4] &&
	nonRedundantWriteLocation[4] < 15)
      initialisedUniform2[nonRedundantWriteLocation[4]] = 1;

    if (0 <= nonRedundantWriteLocation[5] &&
	nonRedundantWriteLocation[5] < 15)
      initialisedUniform2[nonRedundantWriteLocation[5]] = 1;

    if (0 <= nonRedundantWriteLocation[6] &&
	nonRedundantWriteLocation[6] < 64)
      initialisedUniform3[nonRedundantWriteLocation[6]] = 1;

    if (0 <= nonRedundantWriteLocation[7] &&
	nonRedundantWriteLocation[7] < 64 &&
	(nonRedundantWriteLocation[7] & 0x1) == 0)
      initialisedUniform3[nonRedundantWriteLocation[7]] = 0;

    if (0 <= nonRedundantWriteLocation[8] &&
	nonRedundantWriteLocation[8] < 64 &&
	(nonRedundantWriteLocation[8] & 0x1) == 0)
      initialisedUniform3[nonRedundantWriteLocation[8]] = 0;

    if (0 <= nonRedundantWriteLocation[9] &&
	nonRedundantWriteLocation[9] < 64 &&
	(nonRedundantWriteLocation[9] & 0x1) == 0)
      initialisedUniform3[nonRedundantWriteLocation[9]] = 0;


    if ((0 <= nonRedundantWriteLocation[10] &&
	 nonRedundantWriteLocation[10] < 16) &&
	(0 <= nonRedundantWriteLocation[11] &&
	 nonRedundantWriteLocation[11] < 16) &&
	(0 <= nonRedundantWriteLocation[12] &&
	 nonRedundantWriteLocation[12] < 16)) {
      // Check write coallescing and reordering
      // Can re-order writes if the indexes being equal implies the
      // values are equal.

      initialisedNonUniform1[nonRedundantWriteLocation[10]] = 29;
      initialisedNonUniform1[nonRedundantWriteLocation[11]] = 29;

      initialisedNonUniform1[nonRedundantWriteLocation[10]] = nonRedundantWriteLocation[10] + 1;
      initialisedNonUniform1[nonRedundantWriteLocation[11]] = nonRedundantWriteLocation[11] - 1;
      initialisedNonUniform1[nonRedundantWriteLocation[12]] = nonRedundantWriteLocation[12];
    }

    if ((0 <= nonRedundantWriteLocation[13] &&
	 nonRedundantWriteLocation[13] < 16)) {
      initialisedNonUniform2[nonRedundantWriteLocation[13]] &= nonRedundantWriteLocation[13];
    }

    if ((0 <= nonRedundantWriteLocation[14] &&
	 nonRedundantWriteLocation[14] < 16)) {
      initialisedNonUniform3[nonRedundantWriteLocation[14]] += 1;
    }
    if ((0 <= nonRedundantWriteLocation[15] &&
	 nonRedundantWriteLocation[15] < 16)) {
      initialisedNonUniform3[nonRedundantWriteLocation[15]] += 1;
    }


    // Constant access
    // Again, constant index into a fully known but non-constant array
    assert(uninitialisedGlobalArray1[31] == 0);
    assert(uninitialisedGlobalArray1[23] != 23);
    assert(uninitialisedGlobalArray2[37] != 1024);

    assert(initialisedUniform1[11] == 0);
    assert((initialisedUniform2[13] & 0xE) == 0);
    assert(initialisedUniform2[15] == 0);
    assert(initialisedUniform3[17] == 1);

    assert(initialisedNonUniform1[3] - 2 >= 0);
    assert(initialisedNonUniform1[5] - 4 >= 0);
    assert(initialisedNonUniform2[7] == 7);
    assert(initialisedNonUniform3[9] >= 6);

    // Variable access
    int variableNonRedundantUpdateReadLocation[8]; // Non-det

    if (0 <= variableNonRedundantUpdateReadLocation[0] &&
	variableNonRedundantUpdateReadLocation[0] < 256)
      assert(uninitialisedGlobalArray1[variableNonRedundantUpdateReadLocation[0]] >= 0);
    if (0 <= variableNonRedundantUpdateReadLocation[1] &&
	variableNonRedundantUpdateReadLocation[1] < 16)
      assert(uninitialisedGlobalArray2[variableNonRedundantUpdateReadLocation[1]] == 0 ||
	     uninitialisedGlobalArray2[variableNonRedundantUpdateReadLocation[1]] == variableNonRedundantUpdateReadLocation[1]);

    if (10 <= variableNonRedundantUpdateReadLocation[2] &&
	variableNonRedundantUpdateReadLocation[2] < 64)
      assert(initialisedUniform1[variableNonRedundantUpdateReadLocation[2]] == 0);
    if (15 <= variableNonRedundantUpdateReadLocation[3] &&
	variableNonRedundantUpdateReadLocation[3] < 64)
      assert(initialisedUniform2[variableNonRedundantUpdateReadLocation[3]] == 0);
    if (0 <= variableNonRedundantUpdateReadLocation[4] &&
	variableNonRedundantUpdateReadLocation[4] < 64)
      assert(initialisedUniform3[variableNonRedundantUpdateReadLocation[4]] == 1 ||
	     (variableNonRedundantUpdateReadLocation[4] & 0x1) == 0);

    if (0 <= variableNonRedundantUpdateReadLocation[5] &&
	variableNonRedundantUpdateReadLocation[5] < 16)
      assert(initialisedNonUniform1[variableNonRedundantUpdateReadLocation[5]] - variableNonRedundantUpdateReadLocation[5] < 2);
    if (0 <= variableNonRedundantUpdateReadLocation[6] &&
	variableNonRedundantUpdateReadLocation[6] < 16)
      assert(initialisedNonUniform2[variableNonRedundantUpdateReadLocation[6]] == variableNonRedundantUpdateReadLocation[6]);
    if (0 <= variableNonRedundantUpdateReadLocation[7] &&
	variableNonRedundantUpdateReadLocation[7] < 16)
      assert(initialisedNonUniform3[variableNonRedundantUpdateReadLocation[7]] - (15 - variableNonRedundantUpdateReadLocation[7]) < 3);

  }


  return 0;
}
