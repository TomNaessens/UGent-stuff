/*
 * Uitwendige rood-zwart bladzoekboom. Neem als garbagewaarde het gemiddelde van linker- en rechtertop.
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class Tree5 extends AbstractLeafTree {

	@Override
	public void colorGarbageTop(MyVertex garbageTop) {
			if (garbageTop == super.root()) {
				garbageTop.setColor(Vertex.BLACK);
			} else {
				garbageTop.setColor(Vertex.RED);
			}
			
			garbageTop.getLeft().setColor(MyVertex.NOCOLOR);
			garbageTop.getRight().setColor(MyVertex.NOCOLOR);		
	}
}
