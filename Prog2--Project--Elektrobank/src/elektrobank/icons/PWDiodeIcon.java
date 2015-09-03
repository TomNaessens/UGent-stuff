/**
 *
 * @author Tom Naessens
 * TomNaessens@UGent.be
 * 1ste Bachelor Informatica
 * Universiteit Gent
 *
 */

package elektrobank.icons;

import java.awt.Component;
import java.awt.Graphics;
import java.awt.Graphics2D;
import joldespice.components.nonlinear.PWDiode;

public class PWDiodeIcon extends IconPainter {

	public PWDiodeIcon() {
		super(12);
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();

		super.paintIcon(c,g2,x,y);

		g2.drawLine(-6, -8, -6, 8);
		g2.drawLine(-6, -8, 6, 0);
		g2.drawLine(-6, 8, 6, 0);
		g2.drawLine(6, -8, 6, 8);
	}

	@Override
	public String getComponent() {
		return "PWDiode";
	}
}
