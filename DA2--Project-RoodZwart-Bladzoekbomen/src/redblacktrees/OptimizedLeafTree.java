/*
 *
 * Deze klasse is een abstracte bovenklasse voor Tree4 en Tree5.
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public abstract class OptimizedLeafTree extends AbstractLeafTree {

	///////////////////////////////////////////////////////////////////////////////////////////
	///////////////////////////////////   ADD FUNCTIONS    ////////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	
	// Overschrijft de add methode van AbstractRBTree
	@Override
	public boolean add(int value) {

		if (super.root() == null) {
			// Root is null, maak een nieuwe vertex aan en steek hem in de root
			super.setRoot(new MyVertex(Vertex.BLACK, value, null, null, null));
			return true;
		} else {
			MyVertex vertex = super.root();
			MyVertex toAdd = new MyVertex(Vertex.RED, value, null, null, null);

			while (vertex != null) {
				toAdd.setParent(vertex);
				if (value < vertex.getValue()) {
					vertex = vertex.getLeft();
				} else if (value > vertex.getValue()) {
					vertex = vertex.getRight();
				} else {
					return false;
				}
			}

			/*
			 * We zitten zeker in een blad, waar we een nieuw blad aan toevoegen, als de waarden van deze 
			 * overeen komen zitten we zeker met een duplicaat in de inputset, we returnen dus false.
			 */
			if (toAdd.getParent().getValue() == toAdd.getValue()) {
				return false;
			}

			/*
			 * We maken een garbageTop aan met als waarde hat maximum van de 2 waardes, dit heeft
			 * voor later grote voordelen. (Uitleg: zie verslag).
			 */
			MyVertex garbageTop = new MyVertex(Vertex.RED, Math.max(value, toAdd.getParent().getValue()), null, null, null);

			rebalanceGarbageTop(toAdd, garbageTop);

			colorGarbageTop(garbageTop);

			if (garbageTop.getParent() != null && garbageTop.getParent().getColor() == Vertex.RED) {
				standardRebalance(garbageTop);
			}

		}
		return true;
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////   CONTAINS FUNCTIONS   //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public boolean contains(int value) {
		MyVertex vertex = super.root();
		while (vertex.getLeft() != null) { // Niet nodig om te checken op getRight, aangezien elke interne top altijd 2 bladeren heeft
			if (value < vertex.getValue()) {
				vertex = vertex.getLeft();
			} else if(value > vertex.getValue()) {
				vertex = vertex.getRight();
			} else {
				return true;
			}
		}
		return (vertex.getValue() == value);
	}
}
