using System.IO;

namespace PersistentMemoryModule {

  public partial class PersistentMemoryRegion
  {
    private FileStream fileHandle;
    int length;
    public PersistentMemoryRegion(string path)
    {
      length = (int)(new FileInfo(path).Length);
      fileHandle = new FileStream(path, FileMode.Open, FileAccess.ReadWrite, FileShare.None);
    }
    public static PersistentMemoryRegion Create(string path, long length)
    {
      var fileHandle = new FileStream(path, FileMode.Create, FileAccess.ReadWrite, FileShare.None);
      fileHandle.SetLength(length);
      fileHandle.Close();
      return new PersistentMemoryRegion(path);
    }

    public long GetRegionSize()
    {
      return length;
    }

    public void Read(long addr, byte[] bytes, int offset, int num_bytes)
    {
      fileHandle.Seek(addr, SeekOrigin.Begin);
      fileHandle.Read(bytes, offset, num_bytes);
    }

    public void Write(long addr, byte[] bytes, int offset, int num_bytes)
    {
      fileHandle.Seek(addr, SeekOrigin.Begin);
      fileHandle.Write(bytes, offset, num_bytes);
    }

    public void Flush()
    {
      fileHandle.Flush();
    }

  }

}
