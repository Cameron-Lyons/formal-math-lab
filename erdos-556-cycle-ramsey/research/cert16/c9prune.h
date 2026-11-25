// geng generates complements. Its maximum-degree deletion therefore supplies
// a minimum-degree deletion of the graph whose density is being certified.
#define PREPRUNE c9prune
static graph previous_prefix[17][17];
static int valid_prefix[17];
static unsigned conflicts_by_endpoint[17][17];
static unsigned actual_neighbors[17];

static unsigned path_ends(int vertex, unsigned available, int remaining) {
    unsigned choices = actual_neighbors[vertex] & available;
    if (remaining == 1)
        return choices;
    unsigned result = 0;
    while (choices) {
        unsigned next = choices & -choices;
        choices ^= next;
        result |= path_ends(__builtin_ctz(next), available ^ next, remaining - 1);
    }
    return result;
}

static int c9prune(graph *g, int n, int maxn) {
    (void)maxn;
    static const int needed[] = {0, 0, 1, 2, 4, 6, 9, 12, 16, 20, 24, 29, 34, 40, 46, 53, 60};
    int degree_sum = 0;
    for (int i = 0; i < n; ++i)
        degree_sum += POPCOUNT(g[i]);
    if (n * (n - 1) / 2 - degree_sum / 2 < needed[n])
        return 1;
    if (n < 9)
        return 0;

    int old = n - 1;
    unsigned all = (1u << old) - 1;
    graph old_mask = ALLMASK(old);
    int changed = !valid_prefix[old];
    for (int i = 0; i < old; ++i)
        if (previous_prefix[old][i] != (g[i] & old_mask))
            changed = 1;
    if (changed) {
        valid_prefix[old] = 1;
        for (int i = 0; i < old; ++i) {
            previous_prefix[old][i] = g[i] & old_mask;
            actual_neighbors[i] = 0;
            for (int j = 0; j < old; ++j)
                if (i != j && !(g[i] & bit[j]))
                    actual_neighbors[i] |= 1u << j;
        }
        for (int i = 0; i < old; ++i)
            conflicts_by_endpoint[old][i] = path_ends(i, all ^ (1u << i), 7);
    }
    unsigned incident = 0;
    for (int i = 0; i < old; ++i)
        if (!(g[old] & bit[i]))
            incident |= 1u << i;
    while (incident) {
        int i = __builtin_ctz(incident);
        incident &= incident - 1;
        if (conflicts_by_endpoint[old][i] & incident)
            return 1;
    }
    return 0;
}
