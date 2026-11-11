import type {Position} from 'geojson';

/** A longitude outside -180..180 wraps around the antimeridian, so it is brought back. */
export function wrapLongitude(position: Position): number {
  const longitude: number = position[0];
  if (longitude > 180) {
    return longitude - 360;
  }
  if (longitude < -180) {
    return longitude + 360;
  }
  return longitude;
}
