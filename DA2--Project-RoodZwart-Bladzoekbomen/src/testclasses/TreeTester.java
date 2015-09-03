/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be 
 * 2de Bachelor Informatica
 * Universiteit Gent
 *
 */
package testclasses;

import redblacktrees.MyVertex;
import redblacktrees.Vertex;

public class TreeTester {

	public void test(MyVertex root) {

		if(root == null) {
			return;
		}

		assert(root.getColor() == Vertex.BLACK) : "De root is niet zwart";
		

		runTroughVertexes(root);


	}

	public int runTroughVertexes(MyVertex vertex) {

		int zwarteToppenLinks = 0;
		int zwarteToppenRechts = 0;

		if (vertex != null) {

			if (vertex.getColor() == Vertex.RED) {
				if (vertex.getLeft() != null) {
					assert (vertex.getLeft().getColor() != Vertex.RED);
				}
				if (vertex.getRight() != null) {
					assert (vertex.getRight().getColor() != Vertex.RED);
				}
			}

			zwarteToppenLinks = runTroughVertexes(vertex.getLeft());
			zwarteToppenRechts = runTroughVertexes(vertex.getRight());

			if (vertex.getLeft() != null) {
				assert (vertex.getLeft().getValue() < vertex.getValue()) : "Links is groter of gelijk aan ouder.";
			}

			if (vertex.getRight() != null) {
				// > is hier te vervangen door >= bij bladzoekbomen!
				assert (vertex.getRight().getValue() >= vertex.getValue()) : "Rechts is kleiner of gelijk aan ouder.";
			}


			assert (zwarteToppenLinks == zwarteToppenRechts) : "Zwarte toppen links komen niet overeen met zwarte toppen rechts.";

			if (vertex.getColor() == Vertex.BLACK) {
				zwarteToppenLinks++;
				return zwarteToppenLinks;
			} else {
				return zwarteToppenLinks;
			}

		}

		return zwarteToppenLinks;
	}
}
