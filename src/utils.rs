use std::{
    fs::{create_dir, metadata, read_dir, remove_dir_all, File},
    path::Path,
};

/// Temporary directory for unit test
pub struct TempDir {
    dir: String,
}

impl TempDir {
    /// Create a new TempDir
    pub fn new(dir: &str) -> Self {
        remove_dir_all(dir).unwrap_or(()); // ignore error
        create_dir(dir).unwrap_or(()); // ignore error
        Self {
            dir: dir.to_string(),
        }
    }

    /// Return the path of this temporary directory
    pub fn to_string(&self) -> String {
        self.dir.clone()
    }

    /// Return the names of the files in this directory
    pub fn list(&self) -> Vec<String> {
        TempDir::list_dir(&self.dir)
    }

    /// Return the names of the files in `dir`
    pub fn list_dir(dir: &str) -> Vec<String> {
        let mut result = vec![];
        let paths = std::fs::read_dir(Path::new(dir)).unwrap();
        for path in paths {
            result.push(path.unwrap().path().to_str().unwrap().to_string());
        }
        result.sort();
        result
    }

    /// Create a new file in this directory
    pub fn create_file(&self, name: &str) {
        let file_path = Path::new(&self.dir).join(Path::new(name));
        File::create_new(file_path).unwrap();
    }

    /// Return the names of the files in `path` and its subdirectories recursively
    pub fn list_all(path: &Path) -> Vec<String> {
        let mut vec = Vec::new();
        TempDir::_list_files(&mut vec, path);
        vec.sort();
        vec
    }

    fn _list_files(vec: &mut Vec<String>, path: &Path) {
        if metadata(&path).unwrap().is_dir() {
            let paths = read_dir(&path).unwrap();
            for path_result in paths {
                let full_path = path_result.unwrap().path();
                if metadata(&full_path).unwrap().is_dir() {
                    TempDir::_list_files(vec, &full_path);
                } else {
                    vec.push(String::from(full_path.to_str().unwrap()));
                }
            }
        }
    }
}

impl Drop for TempDir {
    fn drop(&mut self) {
        remove_dir_all(&self.dir).unwrap_or(()); // ignore error
    }
}
