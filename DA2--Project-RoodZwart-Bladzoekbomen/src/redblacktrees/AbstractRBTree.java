/*
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

import java.util.Iterator;

public abstract class AbstractRBTree implements Tree {

	private MyVertex root;

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////     ADD FUNCTIONS      //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public boolean add(int value) {
		if (root == null) {
			// Root is null, maak een nieuwe vertex aan en steek deze in de root
			root = new MyVertex(Vertex.BLACK, value, null, null, null);
			return true;
		} else {
			MyVertex vertex = root;
			MyVertex toAdd = new MyVertex(Vertex.RED, value, null, null, null);

			// Daal af naar de top waar de toAdd moet worden aangehangen
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

	// Wordt overschreven afhankelijk van de subklasse
	public void rebalance(MyVertex vertex) {
	}

	/*
	 * De eerste herbalanceringsmethode:
	 * Zolang er een conflict is, voer een herbalancering door en kleur de toppen zoals beschreven
	 * is op pagina 22.
	 * Als daarne de wortel rood is, kleur hem zwart.
	 */
	public void standardRebalance(MyVertex newChild) {
		while (newChild != root && newChild.getParent().getColor() == Vertex.RED) {
			newChild = executeRebalance(newChild);
			defaultColoring(newChild);
		}

		if (newChild == root && newChild.getColor() == Vertex.RED) {
			newChild.setColor(Vertex.BLACK);
		}
	}

	/*
	 * De tweede herbalanceringsmethode:
	 * Zolang er een conflict is, voer een herbalancering door en kleur de toppen zoals beschreven
	 * is op pagina 23.
	 * Als daarna de wortel rood is, kleur hem zwart.
	 */
	public void variantRebalance(MyVertex newChild) {
		MyVertex grandParentOtherChild = null;

		while (newChild != root && newChild.getParent().getColor() == Vertex.RED) {
			grandParentOtherChild = getSibling(newChild.getParent());

			newChild = executeRebalance(newChild);

			if (grandParentOtherChild == null || grandParentOtherChild.getColor() == Vertex.BLACK) {
				variantColoring(newChild);
				return;
			} else {
				defaultColoring(newChild);
			}
		}

		/*
		 * Als we kleuren volgens de variantColoring is dit niet nodig, aangezien we wortel van
		 * de deelboom altijd zwart kleuren. Maar stel dat we nooit de variantColoring kunnen
		 * toepassen, dan passen we steeds de defaultColoring toe waardoor de root van de volledige
		 * boom nog steeds rood kan zijn. Daarom checken we hier nog eens op en kleuren we de root
		 * zwart als hij rood is.
		 */
		if (newChild == root && newChild.getColor() == Vertex.RED) {
			newChild.setColor(Vertex.BLACK);
		}
	}

	// Methode die de wortel van de deelboom rood kleurt en zijn kinderen zwart
	public void defaultColoring(MyVertex newParent) {
		newParent.setColor(Vertex.RED);

		newParent.getLeft().setColor(Vertex.BLACK);
		newParent.getRight().setColor(Vertex.BLACK);
	}

	// Methode die de wortel van de deelboom zwart kleurt en zijn kinderen rood
	public void variantColoring(MyVertex newParent) {
		newParent.setColor(Vertex.BLACK);

		newParent.getLeft().setColor(Vertex.RED);
		newParent.getRight().setColor(Vertex.RED);
	}

	/*
	 * Methode die beslist welk van de 4 herbalanceringsmethodes moet worden toegepast
	 * en de wortel van de nieuwe deelboom teruggeeft
	 */
	public MyVertex executeRebalance(MyVertex newChild) {

		MyVertex child = newChild;
		MyVertex parent = newChild.getParent();
		MyVertex grandParent = newChild.getParent().getParent();

		if (child.getValue() < parent.getValue()) {
			if (parent.getValue() < grandParent.getValue()) {
				newChild = rebalanceLL(newChild, parent, grandParent);
			} else {
				newChild = rebalanceRL(newChild, parent, grandParent);
			}
		} else {
			if (parent.getValue() < grandParent.getValue()) {
				newChild = rebalanceLR(newChild, parent, grandParent);
			} else {
				newChild = rebalanceRR(newChild, parent, grandParent);
			}
		}

		return newChild;
	}

	/* LL: Links Links
	 * parent(B) is linkerkind van grandParent(A)
	 * child(C) is linkerkind van parent(B)
	 *        A			B
	 *       / \		    / \
	 *      B   b4         C   A
	 *     / \            / \ / \		
	 *    C   b3        b1|b2|b3|b4
	 *   / \
	 *  b1  b2
	 */
	public MyVertex rebalanceLL(MyVertex child, MyVertex parent, MyVertex grandParent) {

		grandParent.setLeft(parent.getRight());

		if (parent.getRight() != null) {
			parent.getRight().setParent(grandParent);
		}

		parent.setRight(grandParent);

		if (grandParent == root) {
			root = parent;
			parent.setParent(null);
		} else {
			if (parent.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(parent);
			} else {
				grandParent.getParent().setLeft(parent);
			}
			parent.setParent(grandParent.getParent());
		}

		child.setParent(parent);
		grandParent.setParent(parent);

		return parent;
	}

	/* RL: Rechts Links
	 * parent(B) is rechterkind van grandParent(A)
	 * child(C) is rechterkind van parent(B)
	 *        A			C
	 *       / \		    / \
	 *      b1   B         A   B
	 *          / \       / \ / \	
	 *         C   b4   b1|b2|b3|b4
	 *        / \
	 *       b2  b3	  
	 */
	public MyVertex rebalanceRL(MyVertex child, MyVertex parent, MyVertex grandParent) {

		grandParent.setRight(child.getLeft());
		parent.setLeft(child.getRight());

		if (child.getLeft() != null) {
			child.getLeft().setParent(grandParent);
		}
		if (child.getRight() != null) {
			child.getRight().setParent(parent);
		}

		child.setLeft(grandParent);
		child.setRight(parent);

		if (grandParent == root) {
			root = child;
			child.setParent(null);
		} else {
			if (child.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(child);
			} else {
				grandParent.getParent().setLeft(child);
			}
			child.setParent(grandParent.getParent());
		}

		parent.setParent(child);
		grandParent.setParent(child);

		return child;
	}

	/* LR: Links Rechts
	 * parent(B) is linkerkind van grandParent(A)
	 * child(C) is rechterkind van parent(B)
	 *        A			C
	 *       / \		    / \
	 *      B   b4         B   A
	 *     / \            / \ / \
	 *    b1  C         b1|b2|b3|b4
	 *       / \
	 *      b2  b3
	 */
	public MyVertex rebalanceLR(MyVertex child, MyVertex parent, MyVertex grandParent) {

		grandParent.setLeft(child.getRight());
		parent.setRight(child.getLeft());

		if (child.getRight() != null) {
			child.getRight().setParent(grandParent);
		}
		if (child.getLeft() != null) {
			child.getLeft().setParent(parent);
		}

		child.setRight(grandParent);
		child.setLeft(parent);

		if (grandParent == root) {
			root = child;
			child.setParent(null);
		} else {
			if (child.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(child);
			} else {
				grandParent.getParent().setLeft(child);
			}
			child.setParent(grandParent.getParent());
		}

		parent.setParent(child);
		grandParent.setParent(child);

		return child;
	}

	/* RR: Rechts Rechts
	 * parent(B) is right of grandParent(A)
	 * child(C) is right of parent(B)
	 *        A			B
	 *       / \		    / \
	 *      b1  B          A   C
	 *         / \        / \ / \
	 *        b2  C     b1|b2|b3|b4
	 *           / \
	 *          b3  b4 
	 */
	public MyVertex rebalanceRR(MyVertex child, MyVertex parent, MyVertex grandParent) {

		grandParent.setRight(parent.getLeft());

		if (parent.getLeft() != null) {
			parent.getLeft().setParent(grandParent);
		}

		parent.setLeft(grandParent);


		if (grandParent == root) {
			root = parent;
			parent.setParent(null);
		} else {
			if (parent.getValue() > grandParent.getParent().getValue()) {
				grandParent.getParent().setRight(parent);
			} else {
				grandParent.getParent().setLeft(parent);
			}
			parent.setParent(grandParent.getParent());
		}

		child.setParent(parent);
		grandParent.setParent(parent);

		return parent;
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////    REMOVE FUNCTIONS    //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	
	/**
	 * Verwijdert een top uit een boom.
	 * De onderstaande commentaren die een geval aanduiden komen overeen met de gevallen beschreven 
	 * in het verslag in het puntje 'Theoretische uitwerking: Verwijderen van sleutels'.
	 */
	@Override
	public boolean remove(int value) {
		MyVertex toRemove = root;

		while (toRemove != null && toRemove.getValue() != value) {
			if (value < toRemove.getValue()) {
				toRemove = toRemove.getLeft();
			} else if (value > toRemove.getValue()) {
				toRemove = toRemove.getRight();
			}
		}

		if (toRemove == null || toRemove.getValue() != value) {
			return false;
		} else {
			MyVertex replacementVertex = findReplacementVertex(toRemove);
			toRemove.setValue(replacementVertex.getValue());

			if (replacementVertex == toRemove && replacementVertex == root) {
				// Zeker de root
				if (root.getRight() != null) {
					// GEVAL 2 
					//Wortel met 1 kind rechts: zeker rood
					root.setValue(root.getRight().getValue());
					removeVertex(root.getRight());
				} else {
					// GEVAL 1
					root = null;
				}
				return true;
			}

			if (replacementVertex.getColor() == Vertex.RED) {
				// GEVAL 3
				removeVertex(replacementVertex);
			} else {
				// De replacementtop is zwart. 
				if (replacementVertex.getLeft() != null) {
					/**
					 * Geval 4 (deelgeval 1):
					 * De replacement top is zwart en hij heeft een linkerkind, dan is deze
					 * zeker rood. 
					 */
					replacementVertex.setValue(replacementVertex.getLeft().getValue());
					removeVertex(replacementVertex.getLeft());
				} else if (replacementVertex.getRight() != null) {
					/**
					 * Geval 4 (deelgeval 2):
					 * De replacement top is zwart en hij heeft een rechterkind, dan is deze
					 * zeker rood. 
					 */
					replacementVertex.setValue(replacementVertex.getRight().getValue());
					removeVertex(replacementVertex.getRight());
				} else {
					/**
					 * Geval 5
					 * De replacement top is zwart, maar hij heeft geen linkerkind (en ook
					 * geen rechterkind) om te compenseren als we deze verwijderen. We
					 * maken hier gebruik van de broer van de replacement top om dit probleem
					 * op te lossen.
					 */
					siblingCases(replacementVertex);
					removeVertex(replacementVertex);
				}
			}

			return true;
		}
	}

	// Geeft het grootste linkerkind van een vertex terug of zichzelf als de vertex geen linkerkind heeft
	public MyVertex findReplacementVertex(MyVertex vertex) {
		if (vertex.getLeft() == null) {
			return vertex;
		}
		vertex = vertex.getLeft();
		while (vertex.getRight() != null) {
			vertex = vertex.getRight();
		}
		return vertex;
	}

	// Geeft de broer van de vertex terug of null als deze niet bestaat.
	public MyVertex getSibling(MyVertex vertex) {
		if (vertex.getParent() == null) {
			return null;
		}
		if (vertex.getParent().getLeft() == vertex) {
			return vertex.getParent().getRight();
		}
		return vertex.getParent().getLeft();
	}

	/*
	 * Hulpmethode om te beslissen welke herbalancering moet worden opgeroepen als 
	 * de replacementVertex geen kinderen heeft
	 */
	public void siblingCases(MyVertex replacementVertex) {
		if (replacementVertex.getColor() == Vertex.RED || replacementVertex == root()) {
			replacementVertex.setColor(Vertex.BLACK);
		} else {
			MyVertex sibling = getSibling(replacementVertex);

			if (replacementVertex.getParent().getLeft() == replacementVertex) {
				// replacementVertex is links van de sibling
				if (sibling.getColor() == Vertex.RED) {
					// Deelgeval 1
					// Sibling is rood
					siblingCase1(sibling, replacementVertex);
				} else if (sibling.getLeft() != null && sibling.getLeft().getColor() == Vertex.RED) {
					// Deelgeval 3
					// Sibling heeft een rood linkerkind
					siblingCase3(sibling, replacementVertex);
				} else if (sibling.getRight() != null && sibling.getRight().getColor() == Vertex.RED) {
					// Deelgeval 4
					// Sibling heeft een rood rechterkind
					siblingCase4(sibling, replacementVertex);
				} else {
					// Deelgeval 2
					// Sibling heeft geen rode kinderen
					siblingCase2(sibling, replacementVertex);
				}
			} else {
				// Sibling is links van de replacementVertex
				if (sibling.getColor() == Vertex.RED) {
					// Deelgeval 1
					// Sibling is rood
					siblingCase1Reverse(sibling, replacementVertex);
				} else if (sibling.getRight() != null && sibling.getRight().getColor() == Vertex.RED) {
					// Deelgeval 3
					// Sibling heeft een rood rechterkind
					siblingCase3Reverse(sibling, replacementVertex);
				} else if (sibling.getLeft() != null && sibling.getLeft().getColor() == Vertex.RED) {
					// Deelgeval 4
					// Sibling heeft een rood linkerkind
					siblingCase4Reverse(sibling, replacementVertex);
				} else {
					// Deelgeval 2
					// Sibling heeft geen rode kinderen
					siblingCase2(sibling, replacementVertex);
				}
			}
		}
	}

	/* 
	 * Uitleg voor de volgende methodes: zie verslag, onderdeel 'Theoretische uitwerking:  
	 * Verwijderen van sleutels'.
	 */
	public void siblingCase1(MyVertex sibling, MyVertex replacementVertex) {
		rebalanceRR(sibling.getRight(), sibling, sibling.getParent());
		sibling.setColor(Vertex.BLACK);
		sibling.getRight().setColor(Vertex.BLACK);
		sibling.getLeft().setColor(Vertex.RED);

		siblingCases(replacementVertex);
	}

	public void siblingCase1Reverse(MyVertex sibling, MyVertex replacementVertex) {
		rebalanceLL(sibling.getLeft(), sibling, sibling.getParent());
		sibling.setColor(Vertex.BLACK);
		sibling.getLeft().setColor(Vertex.BLACK);
		sibling.getRight().setColor(Vertex.RED);

		siblingCases(replacementVertex);
	}

	public void siblingCase2(MyVertex sibling, MyVertex replacementVertex) {
		sibling.setColor(Vertex.RED);

		siblingCases(replacementVertex.getParent());
	}

	public void siblingCase3(MyVertex sibling, MyVertex replacementVertex) {
		MyVertex leftSiblingChild = sibling.getLeft();

		leftSiblingChild.setParent(sibling.getParent());

		if (leftSiblingChild.getRight() != null) {
			leftSiblingChild.getRight().setParent(sibling);
		}

		sibling.getParent().setRight(leftSiblingChild);

		sibling.setParent(leftSiblingChild);
		sibling.setLeft(leftSiblingChild.getRight());

		leftSiblingChild.setRight(sibling);

		leftSiblingChild.setColor(Vertex.BLACK);
		sibling.setColor(Vertex.RED);

		siblingCase4(leftSiblingChild, replacementVertex);

	}

	public void siblingCase3Reverse(MyVertex sibling, MyVertex replacementVertex) {
		MyVertex rightSiblingChild = sibling.getRight();

		rightSiblingChild.setParent(sibling.getParent());

		if (rightSiblingChild.getLeft() != null) {
			rightSiblingChild.getLeft().setParent(sibling);
		}

		sibling.getParent().setLeft(rightSiblingChild);

		sibling.setParent(rightSiblingChild);
		sibling.setRight(rightSiblingChild.getLeft());

		rightSiblingChild.setLeft(sibling);

		rightSiblingChild.setColor(Vertex.BLACK);
		sibling.setColor(Vertex.RED);

		siblingCase4Reverse(rightSiblingChild, replacementVertex);

	}

	public void siblingCase4(MyVertex sibling, MyVertex replacementVertex) {
		int colorOfRootOfSubTree = replacementVertex.getParent().getColor();
		rebalanceRR(sibling.getRight(), sibling, sibling.getParent());
		sibling.setColor(colorOfRootOfSubTree);
		sibling.getLeft().setColor(Vertex.BLACK);
		sibling.getRight().setColor(Vertex.BLACK);
	}

	public void siblingCase4Reverse(MyVertex sibling, MyVertex replacementVertex) {
		int colorOfRootOfSubTree = replacementVertex.getParent().getColor();
		rebalanceLL(sibling.getLeft(), sibling, sibling.getParent());
		sibling.setColor(colorOfRootOfSubTree);
		sibling.getRight().setColor(Vertex.BLACK);
		sibling.getLeft().setColor(Vertex.BLACK);
	}
	
	/* 
	 * Verwijdert de gegeven top uit een boom:
	 * - Verwijdert de link tussen parent en kind
	 * - Zet alle verwijzingen naar andere toppen op null, zodat de garbage collector hem snel opkuist
	 */
	public void removeVertex(MyVertex vertex) {
		if (vertex.getParent().getLeft() == vertex) {
			vertex.getParent().setLeft(null);
		} else {
			vertex.getParent().setRight(null);
		}
		// Verwijder alle links naar andere nodes zodat de garbage collector de te verwijderen node kan opruimen
		vertex.setParent(null);
		vertex.setLeft(null);
		vertex.setRight(null);
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////   CONTAINS  FUNCTION   //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public boolean contains(int value) {
		MyVertex vertex = root;
		while (vertex != null) {
			if (value < vertex.getValue()) {
				vertex = vertex.getLeft();
			} else if (value > vertex.getValue()) {
				vertex = vertex.getRight();
			} else {
				return true;
			}
		}
		return false;
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	/////////////////////////////////   ITERATOR  FUNCTION   //////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public Iterator<Integer> iterator() {
		return new TreeIterator(root);
	}

	///////////////////////////////////////////////////////////////////////////////////////////
	////////////////////////////////    GETTERS & SETTERS     /////////////////////////////////
	///////////////////////////////////////////////////////////////////////////////////////////
	@Override
	public MyVertex root() {
		return root;
	}

	public void setRoot(MyVertex vertex) {
		root = vertex;
	}
}
