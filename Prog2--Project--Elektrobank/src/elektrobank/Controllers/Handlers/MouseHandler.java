/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.Controllers.Handlers;

import java.awt.Graphics;
import javax.swing.event.MouseInputListener;

public interface MouseHandler extends MouseInputListener {

	public void paint(Graphics g);

}
