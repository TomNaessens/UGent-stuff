/*
 * Inwendige rood-zwart bladzoekboom. Neem als garbagewaarde het gemiddelde van linker- en rechtertop.
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class Tree4 extends AbstractLeafTree {

	@Override
	/*
	 * Eigenlijk was het ook mogelijk geweest om deze methode in AbstractLeafTree te steken
	 * en dan Tree5 deze methode te laten overschrijven, maar om het verschil tussen 4 en 5
	 * duidelijk te maken heb ik gekozen een lege implementatie in AbstractLeafTree te steken.
	 */
	public void colorGarbageTop(MyVertex garbageTop) {
			if (garbageTop == super.root()) {
				garbageTop.setColor(Vertex.BLACK);
			} else {
				garbageTop.setColor(Vertex.RED);
			}
			
			garbageTop.getLeft().setColor(Vertex.BLACK);
			garbageTop.getRight().setColor(Vertex.BLACK);		
	}
}
