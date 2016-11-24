typedef enum _MetadataSource MetadataSource;

enum _MetadataSource {
  SOURCE_UNKNOWN = 0,
  SOURCE_CDTEXT,
  SOURCE_FREEDB,
  SOURCE_MUSICBRAINZ,
  SOURCE_FALLBACK
};

struct _AlbumDetails {
  MetadataSource metadata_source;
};

static int A[sizeof(struct _AlbumDetails)];

int main()
{
}
