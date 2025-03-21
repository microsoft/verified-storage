def count_shard_occurrences(filename):
    """
    Count occurrences of 'shard 0' and 'shard 1' in a given file.
    
    Args:
        filename (str): Path to the file to be analyzed
    
    Returns:
        dict: A dictionary with counts of 'shard 0' and 'shard 1'
    """
    shard_counts = {
        'shard 0': 0,
        'shard 1': 0
    }
    
    try:
        with open(filename, 'r') as file:
            content = file.read()
            shard_counts['shard 0'] = content.count('shard 0')
            shard_counts['shard 1'] = content.count('shard 1')
    
    except FileNotFoundError:
        print(f"Error: File '{filename}' not found.")
    except IOError:
        print(f"Error: Could not read file '{filename}'.")
    
    return shard_counts

# Example usage
if __name__ == '__main__':
    import sys
    
    if len(sys.argv) != 2:
        print("Usage: python script.py <filename>")
        sys.exit(1)
    
    filename = sys.argv[1]
    results = count_shard_occurrences(filename)
    
    print(f"'shard 0' occurrences: {results['shard 0']}")
    print(f"'shard 1' occurrences: {results['shard 1']}")