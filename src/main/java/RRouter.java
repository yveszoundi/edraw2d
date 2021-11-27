
import java.util.List;

public class RRouter {

	@SuppressWarnings("rawtypes")
	public RPointList solveFor(List obstacles, List bendpoints, int x1, int y1, int x2, int y2) {
		RPoint start = new RPoint(x1, y1);
		RPoint end = new RPoint(x2, y2);

		RShortestPathRouter router = new RShortestPathRouter();

		for (int i = 0; i < obstacles.size(); i++) {
			List l = (List) obstacles.get(i);

			int x = Integer.parseInt(l.get(0).toString());
			int y = Integer.parseInt(l.get(1).toString());
			int w = Integer.parseInt(l.get(2).toString());
			int h = Integer.parseInt(l.get(3).toString());

			router.addObstacle(new RRectangle(x, y, w, h));
		}

		RPath path = new RPath(start, end);
		RPointList bendPointList = new RPointList(bendpoints.size());
		for (int i = 0; i < bendpoints.size(); i++) {
			List l = (List) bendpoints.get(i);
			int x = Integer.parseInt(l.get(0).toString());
			int y = Integer.parseInt(l.get(1).toString());
			bendPointList.addPoint(x, y);

		}
		
		path.setBendPoints(bendPointList);
		router.addPath(path);

		router.solve();

		return path.getPoints();
	}

}
