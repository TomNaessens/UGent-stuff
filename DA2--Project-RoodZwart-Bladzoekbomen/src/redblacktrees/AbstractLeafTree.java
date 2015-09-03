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

import java.util.Iterator;

public abstract class AbstractLeafTree extends AbstractRBTree {

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
				} else if (value >= vertex.getValue()) {
					vertex = vertex.getRight();
				}
			}

			/*
			 * We zitten zeker in een blad, waar we een blad aan toevoegen, als de waarden van deze 
			 * overeen komen zitten we zeker met een duplicaat in de inputset, we returnen dus false.
			 */
			if (toAdd.getParent().getValue() == toAdd.getValue()) {
				return false;
			}

			int gemiddelde;
			
			gemiddelde = (int) Math.ceil((toAdd.getValue() + toAdd.getParent().getValue()) / 2.0);
			MyVertex garbageTop = new MyVertex(Vertex.RED, gemiddelde, null, null, null);

			rebalanceGarbageTop(toAdd, garbageTop);
			colorGarbageTop(garbageTop);

			if (garbageTop.getParent() != null && garbageTop.getParent().getColor() == Vertex.RED) {
				standardRebalance(garbageTop);
			}

		}
		return true;
	}
	
	public MyVertex rebalanceGarbageTop(MyVertex toAdd, MyVertex garbageTop) {

		garbageTop.setParent(toAdd.getParent().getParent());
		if (garbageTop.getParent() == null) {
			super.setRoot(garbageTop);
		} else {
			if (garbageTop.getValue() > garbageTop.getParent().getValue()) {
				toAdd.getParent().getParent().setRight(garbageTop);
			} else {
				toAdd.getParent().getParent().setLeft(garbageTop);
			}
		}

		if (toAdd.getValue() >= garbageTop.getValue()) {
			garbageTop.setLeft(toAdd.getParent());
			garbageTop.setRight(toAdd);
		} else {
			garbageTop.setLeft(toAdd);
			garbageTop.setRight(toAdd.getParent());
		}

		toAdd.getParent().setParent(garbageTop);
		toAdd.setParent(garbageTop);

		return garbageTop;
	}

	// Wordt overschreven in subklasses
	public void colorGarbageTop(MyVertex garbageTop) {
		
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////    REMOVE FUNCTIONS    //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	// Moest niet geïmplementeerd worden
	public boolean remove(int value) {
		throw new UnsupportedOperationException();
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
			} else {
				vertex = vertex.getRight();
			}
		}
		return (vertex.getValue() == value);
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////   ITERATOR  FUNCTION   //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public Iterator<Integer> iterator() {
		return new LeafIterator(super.root());
	}
	
	
}
