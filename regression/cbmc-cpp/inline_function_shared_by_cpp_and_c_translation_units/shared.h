#ifdef __cplusplus
extern "C"
{
#endif
  struct stream
  {
    int position;
  };
  inline int stream_position(struct stream *s)
  {
    return s->position;
  }
  int c_side(struct stream *s);
#ifdef __cplusplus
}
#endif
