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
import joldespice.components.linear.CurrentSource;

public class CurrentSourceIcon extends IconPainter {

	public CurrentSourceIcon() {
		super(20);
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();

		super.paintIcon(c,g2,x,y);

		g2.drawOval(-10, -10, 20, 20); // Ovaal

		g2.drawLine(-5, 0, 5, 0);
		g2.drawLine(1, -3, 5, 0);
		g2.drawLine(1, 3, 5, 0);
	}

	@Override
	public String getComponent() {
		return "CurrentSource";
	}
}
