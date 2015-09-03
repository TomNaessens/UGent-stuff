
public interface PartitionSolver {

    /**
     * Bepaalt op welke manier de gegeven rij optimaal in k partities kan
     * gesplitst worden.
     *
     * @param row de gegeven rij.
     * @param k het aantal gewenste partities.
     *
     * @return een tabel met lengte k-1 (!) die de index van het eerste
     * element van elke nieuwe rij weergeeft.
     */
    int[] solve(int[] row, int k);

}
