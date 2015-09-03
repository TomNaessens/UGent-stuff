/*
 * Implementatie van een gewone rood-zwart boom die vanaf een bepaalde diepte de geoptimaliseerde kleuring gebruikt
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class Tree3 extends AbstractRBTree {

	int maxDiepte;

	@Override
	public boolean add(int value) {
		int tempDiepte = 0;

		if (super.root() == null) {
			// Root is null, maak een nieuwe vertex aan en steek deze in de root
			super.setRoot(new MyVertex(Vertex.BLACK, value, null, null, null));
			return true;
		} else {
			MyVertex vertex = super.root();
			MyVertex toAdd = new MyVertex(Vertex.RED, value, null, null, null);

			// Daal af naar de top waar de toAdd moet worden aangehangen
			while (vertex != null) {
				toAdd.setParent(vertex);
				tempDiepte++;
				if (value < vertex.getValue()) {
					vertex = vertex.getLeft();
				} else if (value > vertex.getValue()) {
					vertex = vertex.getRight();
				} else {
					return false;
				}
			}

			// Update de diepte indien nodig
			if (tempDiepte > maxDiepte) {
				maxDiepte = tempDiepte;
			}

			// Beslis als de top links of rechts van zijn parent moet komen
			if (toAdd.getValue() < toAdd.getParent().getValue()) {
				toAdd.getParent().setLeft(toAdd);
			} else {
				toAdd.getParent().setRight(toAdd);
			}

			/*
			 * De kleur van de toegevoegde top is rood. Als de kleur van de parent van 
			 * toAdd rood is moeten we herbalanceren
			 */
			if (toAdd.getParent().getColor() == Vertex.RED) {
				rebalance(toAdd);
			}

		}
		return true;
	}

	@Override
	public void rebalance(MyVertex vertex) {

		int teller = 0;

		// Zolang de waarde van de parameter niet is overschreden, voer de gewone uit.
		while (vertex != super.root() && vertex.getParent().getColor() == Vertex.RED && teller < maxDiepte/2) {
			vertex = executeRebalance(vertex);
			defaultColoring(vertex);
			teller++;

			if (vertex == super.root() && vertex.getColor() == Vertex.RED) {
				vertex.setColor(Vertex.BLACK);
				return;
			}
		}

		super.variantRebalance(vertex);

	}
}
