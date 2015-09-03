/**
 * Uitwendige rood-zwart bladzoekboomboom. Neem als garbagewaarde het grootste van linker- en rechtertop.
 * 
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package redblacktrees;

public class Tree7 extends OptimizedLeafTree {

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
