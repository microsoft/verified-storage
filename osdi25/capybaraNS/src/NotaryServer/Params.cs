using System;
using System.Net;

namespace NotaryServer
{
  public class Params
  {
    private bool setup;
    private bool verbose;
    private string fileName;

    public Params()
    {
      setup = false;
      verbose = false;
      fileName = "";
    }

    public bool Setup { get { return setup; } }
    public string FileName { get { return fileName; } }
    public bool Verbose { get { return verbose; } }

    public bool Validate()
    {
      if (FileName.Length == 0) {
        Console.WriteLine("ERROR - Missing filename parameter");
        return false;
      }
      return true;
    }

    public bool ProcessCommandLineArgument(string arg)
    {
      var pos = arg.IndexOf("=");
      if (pos < 0) {
        Console.WriteLine("Invalid argument {0}", arg);
        return false;
      }
      var key = arg.Substring(0, pos).ToLower();
      var value = arg.Substring(pos + 1);
      return SetValue(key, value);
    }

    private bool SetBoolValue(string key, string value, ref bool p)
    {
      if (value == "false") {
        p = false;
        return true;
      }
      else if (value == "true") {
        p = true;
        return true;
      }
      else {
        Console.WriteLine("ERROR - Invalid {0} value {1} - should be false or true", key, value);
        return false;
      }
    }

    private bool SetValue(string key, string value)
    {
      if (key == "verbose") {
        return SetBoolValue(key, value, ref verbose);
      }

      if (key == "setup") {
        return SetBoolValue(key, value, ref setup);
      }

      if (key == "filename") {
        fileName = value;
        return true;
      }

      Console.WriteLine("Invalid argument key {0}", key);
      return false;
    }
  }
}
