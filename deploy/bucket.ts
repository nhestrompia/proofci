/** Create the private evidence bucket if it is missing. Versioning must never be enabled. */
import { CreateBucketCommand, GetBucketVersioningCommand, HeadBucketCommand, S3Client } from '@aws-sdk/client-s3';

const bucket = process.env.PROOFCI_S3_BUCKET, region = process.env.PROOFCI_S3_REGION, endpoint = process.env.PROOFCI_S3_ENDPOINT;
if (!bucket || !region) throw new Error('Set PROOFCI_S3_BUCKET and PROOFCI_S3_REGION');
const s3 = new S3Client({ region, endpoint, forcePathStyle: Boolean(endpoint) });
for (let attempt = 1; ; attempt++) {
  try {
    try { await s3.send(new HeadBucketCommand({ Bucket: bucket })); }
    catch (error) {
      if (!(error instanceof Error) || (error.name !== 'NotFound' && error.name !== 'NoSuchBucket')) throw error;
      await s3.send(new CreateBucketCommand({ Bucket: bucket }));
      process.stdout.write(`Created bucket ${bucket}\n`);
    }
    break;
  } catch (error) {
    if (attempt >= 30) throw error;
    await new Promise(resolve => setTimeout(resolve, 1000));
  }
}
if ((await s3.send(new GetBucketVersioningCommand({ Bucket: bucket }))).Status) throw new Error('Evidence bucket versioning must never be enabled');
process.stdout.write(`Bucket ${bucket} is ready without versioning\n`);
