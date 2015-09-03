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
import joldespice.components.linear.SquareWave;

public class SquareWaveIcon extends IconPainter {

	public SquareWaveIcon() {
		super(20);
	}

	@Override
	public void paintIcon(Component c, Graphics g, int x, int y) {
		Graphics2D g2 = (Graphics2D) g.create();

		super.paintIcon(c, g2, x, y);

		g2.drawOval(-10, -10, 20, 20); // Ovaal
		g2.drawLine(-4, 4, -4, -4); // Vert. lijn links ovaal
		g2.drawLine(-4, -4, 0, -4); // Hor. lijn links ovaal
		g2.drawLine(0, 4, 0, -4); // Vert. lijn midden ovaal
		g2.drawLine(0, 4, 4, 4); // Hor. lijn rechts ovaal
		g2.drawLine(4, 4, 4, -4); // Vert. lijn rechts ovaal
	}

	@Override
	public String getComponent() {
		return "SquareWave";
	}
}
