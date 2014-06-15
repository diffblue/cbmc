struct adpcm_state {
    char	index;		/* Index into stepsize table */
};

void adpcm_coder(struct adpcm_state *state)
{
    int index;			/* Current step change index */
    index = state->index;
    state->index = index;
}

struct adpcm_state state;

main() {
    while(1) {
	adpcm_coder(&state);
    }
}
